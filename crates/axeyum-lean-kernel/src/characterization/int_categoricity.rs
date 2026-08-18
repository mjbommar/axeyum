//! **Categoricity of `Int`**: the half that was missing.
//!
//! [`super::int`] proves that the constructed `Int` *has* the properties that
//! separate `ℤ` from its neighbours (no junk, generation by `1`, discreteness
//! everywhere, total order, non-triviality) and that maps out of it are
//! **unique**. That is the uniqueness half of a universal property. It does not
//! say those properties *determine* `Int`: for that you must be able to build a
//! map `Int → R` out of an arbitrary target `R`'s own data and show it is a
//! bijection.
//!
//! This module builds that map and proves it.
//!
//! ## The category `Int` is initial in
//!
//! A **`ℤ`-structure** is a carrier `R : Sort u` with a point `e : R` and two
//! endomorphisms `up down : R → R` that are mutually inverse:
//!
//! ```text
//! left_inverse  : ∀ x, down (up x) = x
//! right_inverse : ∀ x, up (down x) = x
//! ```
//!
//! i.e. a pointed set with an automorphism. `Int` is the **initial** such
//! structure: [`IntCategoricity::iter`] is a map into any of them,
//! [`IntCategoricity::iter_zero`], [`IntCategoricity::iter_succ`] and
//! [`IntCategoricity::iter_pred`] are its three structure-preservation
//! equations (the *existence* half), and the already-proved
//! `Int.Characterization.rec_unique` is the *uniqueness* half. Note which
//! hypothesis each equation needs: `iter_succ` needs only `right_inverse` and
//! `iter_pred` only `left_inverse`, and the negative controls pin that down.
//!
//! ## Categoricity
//!
//! Initiality alone does not pin `Int` up to isomorphism — `ℤ/n` with `e = 0`,
//! `up = (+1)`, `down = (−1)` is a `ℤ`-structure too, and so is `ℤ ⊔ ℤ`. Two
//! further hypotheses do it, and each rules out exactly one of those:
//!
//! ```text
//! generation : ∀ (P : R → Prop), P e → (∀ x, P x → P (up x)) → (∀ x, P x → P (down x)) → ∀ x, P x
//! aperiodic  : ∀ (n : Nat), e ≠ Nat.Peano.iter R e up (n+1)
//! ```
//!
//! `generation` rules out `ℤ ⊔ ℤ` (a second component is never reached);
//! `aperiodic` rules out `ℤ/n` (the point returns to itself after `n` steps).
//! [`IntCategoricity::categorical`] proves that under all four hypotheses the
//! comparison map preserves the structure and is injective and surjective —
//! **second-order categoricity for `ℤ`**, stated inside the kernel and
//! universe-polymorphic, exactly as `Nat.Peano.categorical` is for `ℕ`.
//!
//! `aperiodic` quantifies over *our* `Nat`. That is not circular and it is not
//! a weakening: `Nat.Peano.categorical` proves our `Nat` is the natural numbers
//! up to unique isomorphism, so "no positive iterate of `up` returns `e` to
//! itself" means what it says.
//!
//! ## Two strengths of "isomorphism", and which one is which
//!
//! `Nat.Peano.categorical` proves its comparison map injective and surjective,
//! but surjectivity is a `Prop`-level `∃` and no inverse **function** is
//! extracted. [`IntCategoricity::categorical`] has exactly the same shape, and
//! for the same reason: `generation` is a `Prop`-valued induction principle, so
//! it can prove `∀ y, ∃ t, iter t = y` and cannot define a function `R → Int`.
//! With only `Prop`-valued generation on the target that is the strongest form
//! available, and claiming more would be false.
//!
//! [`IntCategoricity::iso`] is the stronger form, at the cost of an honest extra
//! hypothesis: given **any** structure-preserving `psi : R → Int` it proves
//! `iter ∘ psi = id_R` **and** `psi ∘ iter = id_Int` — a constructed pair of
//! mutually inverse maps, not a `Prop`-level `∃`. So: any back-map is
//! automatically a two-sided inverse, and it is unique (`rec_unique`). What is
//! *not* proved, and cannot be from these hypotheses, is that a back-map
//! exists; that is precisely the content `Prop`-valued generation withholds.
//!
//! ## Non-vacuity is part of the package, not part of the test suite
//!
//! A categoricity theorem whose hypotheses nothing satisfies is axiom-free and
//! worthless. [`IntCategoricity::categorical_at_int`] instantiates `categorical`
//! at `(Int, 0, (·+1), (·−1))` with the four hypotheses discharged by real
//! theorems — the mutual inverses from the ring laws, generation from
//! `Int.Characterization.induction`, aperiodicity from
//! `Nat.Peano.zero_ne_succ` through `Int.natAbs` — and pushes the result back
//! through the trusted gate. It is a declaration of the shipped package, so it
//! is checked on every build and printed by `characterization_status`, not left
//! to a test that someone may stop running.

// Proof scripts are long, straight-line term constructions over short
// mathematical names; splitting them would obscure the derivation they mirror.
#![allow(
    clippy::many_single_char_names,
    clippy::similar_names,
    clippy::too_many_lines,
    clippy::type_complexity
)]

use crate::KernelError;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::nat_prelude::NatOps;

use super::int::{iadd, ineg, ione, izero, minus_one, neg_succ, of_nat, plus_one};
use super::nat::NatCharacterization;
use super::ops::CharDev;
use super::{IntCharacterization, Weakening};

/// Delta height for `Int.Characterization.iter`: it calls `Nat.Peano.iter`
/// (height 40), so it must outrank it.
const ITER_HEIGHT: u16 = 41;

/// The interned names of the `Int` categoricity package.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct IntCategoricity {
    /// The `Int.Characterization` namespace root (shared with [`IntCharacterization`]).
    pub root: NameId,
    /// The universe parameter `u` shared by the carrier-generic declarations.
    pub uparam: NameId,
    /// `iter.{u} : ∀ (R : Sort u), R → (R → R) → (R → R) → Int → R` — the
    /// comparison map, i.e. the **existence** half of the universal property.
    pub iter: NameId,
    /// `iter R e up down 0 = e`.
    pub iter_zero: NameId,
    /// `iter (t+1) = up (iter t)`, from `up ∘ down = id`.
    pub iter_succ: NameId,
    /// `iter (t−1) = down (iter t)`, from `down ∘ up = id`.
    pub iter_pred: NameId,
    /// `up` is injective, from `down ∘ up = id`.
    pub up_injective: NameId,
    /// `up`-iterates of `e` are pairwise distinct.
    pub iter_up_injective: NameId,
    /// `up (down^(n+1) e) = down^n e`, one step of the inverse law.
    pub shift: NameId,
    /// No `up`-iterate of `e` is a `down`-iterate of `e` unless both are `e`.
    pub cross: NameId,
    /// `down`-iterates of `e` are pairwise distinct.
    pub iter_down_injective: NameId,
    /// The comparison map is injective.
    pub injective: NameId,
    /// The comparison map is surjective (a `Prop`-level `∃`).
    pub surjective: NameId,
    /// **Categoricity** — the comparison map preserves the structure and is a
    /// bijection, for every aperiodic generated `ℤ`-structure.
    pub categorical: NameId,
    /// Any structure-preserving map back is a two-sided inverse: the
    /// constructed-isomorphism form.
    pub iso: NameId,
    /// `Nat.Peano.iter Int 0 (·+1) k = Int.ofNat k`, the bridge the
    /// non-vacuity witness needs.
    pub iter_at_int: NameId,
    /// **Non-vacuity** — `categorical` instantiated at `(Int, 0, (·+1), (·−1))`
    /// with every hypothesis discharged by a real theorem.
    pub categorical_at_int: NameId,
}

/// A `ℤ`-structure's data, threaded through the proof scripts.
#[derive(Debug, Clone, Copy)]
struct Structure {
    /// The universe level of the carrier.
    level: LevelId,
    /// `Nat.Peano.iter`.
    nat_iter: NameId,
    /// `Int.Characterization.iter`.
    iter: NameId,
    /// The carrier `R`.
    carrier: ExprId,
    /// The point `e : R`.
    point: ExprId,
    /// `up : R → R`.
    up: ExprId,
    /// `down : R → R`.
    down: ExprId,
}

/// A fresh `(R, e, up, down)` binder head.
struct Head {
    /// The four binders, in order.
    binders: [(u64, ExprId); 4],
    /// The structure they name.
    s: Structure,
}

/// `Nat.Peano.iter.{u} R e up n`, i.e. `up^n e`.
fn uiter(dev: &mut CharDev<'_>, s: Structure, n: ExprId) -> ExprId {
    let head = dev.kernel().const_(s.nat_iter, vec![s.level]);
    dev.apply(head, &[s.carrier, s.point, s.up, n])
}

/// `Nat.Peano.iter.{u} R e down n`, i.e. `down^n e`.
fn diter(dev: &mut CharDev<'_>, s: Structure, n: ExprId) -> ExprId {
    let head = dev.kernel().const_(s.nat_iter, vec![s.level]);
    dev.apply(head, &[s.carrier, s.point, s.down, n])
}

/// The comparison map `iter R e up down t`.
fn phi(dev: &mut CharDev<'_>, s: Structure, t: ExprId) -> ExprId {
    let head = dev.kernel().const_(s.iter, vec![s.level]);
    dev.apply(head, &[s.carrier, s.point, s.up, s.down, t])
}

/// A fresh binder head for a carrier-generic declaration.
fn fresh_head(
    dev: &mut CharDev<'_>,
    level: LevelId,
    sort: ExprId,
    nat_iter: NameId,
    iter: NameId,
) -> Head {
    let r_fv = dev.fresh_fvar();
    let carrier = dev.kernel().fvar(r_fv);
    let e_fv = dev.fresh_fvar();
    let point = dev.kernel().fvar(e_fv);
    let endo = dev.arrow(carrier, carrier);
    let up_fv = dev.fresh_fvar();
    let up = dev.kernel().fvar(up_fv);
    let down_fv = dev.fresh_fvar();
    let down = dev.kernel().fvar(down_fv);
    Head {
        binders: [
            (r_fv, sort),
            (e_fv, carrier),
            (up_fv, endo),
            (down_fv, endo),
        ],
        s: Structure {
            level,
            nat_iter,
            iter,
            carrier,
            point,
            up,
            down,
        },
    }
}

/// `∀ (x : R), down (up x) = x`.
fn left_inverse_ty(dev: &mut CharDev<'_>, s: Structure) -> ExprId {
    let x_fv = dev.fresh_fvar();
    let x = dev.kernel().fvar(x_fv);
    let inner = dev.apply(s.up, &[x]);
    let outer = dev.apply(s.down, &[inner]);
    let body = dev.eq_at(s.level, s.carrier, outer, x);
    dev.pi_fv(x_fv, s.carrier, body)
}

/// `∀ (x : R), up (down x) = x`.
fn right_inverse_ty(dev: &mut CharDev<'_>, s: Structure) -> ExprId {
    let x_fv = dev.fresh_fvar();
    let x = dev.kernel().fvar(x_fv);
    let inner = dev.apply(s.down, &[x]);
    let outer = dev.apply(s.up, &[inner]);
    let body = dev.eq_at(s.level, s.carrier, outer, x);
    dev.pi_fv(x_fv, s.carrier, body)
}

/// `∀ (P : R → Prop), P e → (∀ x, P x → P (up x)) → (∀ x, P x → P (down x)) → ∀ x, P x`.
fn generation_ty(dev: &mut CharDev<'_>, s: Structure) -> ExprId {
    let prop = dev.prop_ty();
    let p_ty = dev.arrow(s.carrier, prop);
    let p_fv = dev.fresh_fvar();
    let p = dev.kernel().fvar(p_fv);
    let base = dev.apply(p, &[s.point]);
    let step = |d: &mut CharDev<'_>, f: ExprId| {
        let x_fv = d.fresh_fvar();
        let x = d.kernel().fvar(x_fv);
        let p_x = d.apply(p, &[x]);
        let shifted = d.apply(f, &[x]);
        let p_shifted = d.apply(p, &[shifted]);
        let body = d.arrow(p_x, p_shifted);
        d.pi_fv(x_fv, s.carrier, body)
    };
    let up_step = step(dev, s.up);
    let down_step = step(dev, s.down);
    let tail = {
        let x_fv = dev.fresh_fvar();
        let x = dev.kernel().fvar(x_fv);
        let body = dev.apply(p, &[x]);
        dev.pi_fv(x_fv, s.carrier, body)
    };
    let after_down = dev.arrow(down_step, tail);
    let after_up = dev.arrow(up_step, after_down);
    let after_base = dev.arrow(base, after_up);
    dev.pi_fv(p_fv, p_ty, after_base)
}

/// `∀ (n : Nat), Not (Eq R e (up^(n+1) e))` — `up` has no finite period at `e`.
fn aperiodic_ty(dev: &mut CharDev<'_>, s: Structure) -> ExprId {
    let nat = dev.nat_ty();
    let n_fv = dev.fresh_fvar();
    let n = dev.kernel().fvar(n_fv);
    let succ_n = dev.succ(n);
    let iterated = uiter(dev, s, succ_n);
    let equation = dev.eq_at(s.level, s.carrier, s.point, iterated);
    let negated = dev.not_of(equation);
    dev.pi_fv(n_fv, nat, negated)
}

/// `Int.rec.{0}` case analysis with a `Prop`-valued motive.
fn int_cases(
    dev: &mut CharDev<'_>,
    motive_body: &dyn Fn(&mut CharDev<'_>, ExprId) -> ExprId,
    of_nat_case: &dyn Fn(&mut CharDev<'_>, ExprId) -> ExprId,
    neg_succ_case: &dyn Fn(&mut CharDev<'_>, ExprId) -> ExprId,
    target: ExprId,
) -> ExprId {
    let int_ty = dev.int_ty();
    let nat = dev.nat_ty();
    let motive = {
        let x_fv = dev.fresh_fvar();
        let x = dev.kernel().fvar(x_fv);
        let body = motive_body(dev, x);
        dev.lam_fv(x_fv, int_ty, body)
    };
    let branch_of = {
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let body = of_nat_case(dev, n);
        dev.lam_fv(n_fv, nat, body)
    };
    let branch_neg = {
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let body = neg_succ_case(dev, n);
        dev.lam_fv(n_fv, nat, body)
    };
    let zero_lvl = dev.level_zero();
    let rec_name = dev.int_prelude().rec;
    let rec = dev.kernel().const_(rec_name, vec![zero_lvl]);
    dev.apply(rec, &[motive, branch_of, branch_neg, target])
}

/// Declare the whole `Int` categoricity package.
///
/// # Errors
///
/// Returns the trusted gate's rejection. Every `Err` here means the kernel
/// **refused** one of the categoricity proofs.
pub(super) fn declare(
    dev: &mut CharDev<'_>,
    nat: NatCharacterization,
    int: IntCharacterization,
    weaken: Weakening,
) -> Result<IntCategoricity, KernelError> {
    let root = int.root;
    let names = IntCategoricity {
        root,
        uparam: int.uparam,
        iter: dev.kernel().name_str(root, "iter"),
        iter_zero: dev.kernel().name_str(root, "iter_zero"),
        iter_succ: dev.kernel().name_str(root, "iter_succ"),
        iter_pred: dev.kernel().name_str(root, "iter_pred"),
        up_injective: dev.kernel().name_str(root, "up_injective"),
        iter_up_injective: dev.kernel().name_str(root, "iter_up_injective"),
        shift: dev.kernel().name_str(root, "shift"),
        cross: dev.kernel().name_str(root, "cross"),
        iter_down_injective: dev.kernel().name_str(root, "iter_down_injective"),
        injective: dev.kernel().name_str(root, "injective"),
        surjective: dev.kernel().name_str(root, "surjective"),
        categorical: dev.kernel().name_str(root, "categorical"),
        iso: dev.kernel().name_str(root, "iso"),
        iter_at_int: dev.kernel().name_str(root, "iter_at_int"),
        categorical_at_int: dev.kernel().name_str(root, "categorical_at_int"),
    };

    let nat_ty = dev.nat_ty();
    let int_ty = dev.int_ty();
    let one_lvl = dev.level_one();
    let u_lvl = dev.level_of(names.uparam);
    let sort_u = dev.sort_at(u_lvl);
    let true_ty = dev.true_ty();
    let nat_iter = nat.iter;

    // ---- the comparison map --------------------------------------------------
    //
    // `iter R e up down` sends `ofNat n` to `up^n e` and `negSucc n` to
    // `down^(n+1) e`. Both are `Nat.Peano.iter`, so the two `Nat`-side
    // computation rules hold definitionally and only the *crossing* equations
    // (`negSucc 0 + 1 = 0` and `ofNat (k+1) − 1 = ofNat k`) need the inverse
    // laws.
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);
        let mut binders = head.binders.to_vec();
        binders.push((t_fv, int_ty));
        let ty = dev.close_pi(&binders, s.carrier);

        let motive = dev.lam_const(int_ty, s.carrier);
        let branch_of = {
            let n_fv = dev.fresh_fvar();
            let n = dev.kernel().fvar(n_fv);
            let body = uiter(dev, s, n);
            dev.lam_fv(n_fv, nat_ty, body)
        };
        let branch_neg = {
            let n_fv = dev.fresh_fvar();
            let n = dev.kernel().fvar(n_fv);
            let succ_n = dev.succ(n);
            let body = diter(dev, s, succ_n);
            dev.lam_fv(n_fv, nat_ty, body)
        };
        let rec_name = dev.int_prelude().rec;
        let rec = dev.kernel().const_(rec_name, vec![u_lvl]);
        let body = dev.apply(rec, &[motive, branch_of, branch_neg, t]);
        let value = dev.close_lam(&binders, body);
        dev.declare_definition_u(names.iter, vec![names.uparam], ty, value, ITER_HEIGHT)?;
    }

    // ---- iter 0 = e ----------------------------------------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let zero = izero(dev);
        let applied = phi(dev, s, zero);
        let equation = dev.eq_at(u_lvl, s.carrier, applied, s.point);
        let statement = dev.close_pi(&head.binders, equation);
        let proof = dev.refl_at(u_lvl, s.carrier, s.point);
        let value = dev.close_lam(&head.binders, proof);
        dev.declare_theorem_u(names.iter_zero, vec![names.uparam], statement, value)?;
    }

    // ---- iter (t+1) = up (iter t) -------------------------------------------
    //
    // `ofNat` is definitional; the `negSucc` branch is where `up ∘ down = id`
    // is used, because `negSucc n + 1` crosses zero.
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let hypothesis_ty = if weaken == Weakening::IntIterSuccDropInverse {
            true_ty
        } else {
            right_inverse_ty(dev, s)
        };
        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);

        let goal = |d: &mut CharDev<'_>, x: ExprId| {
            let shifted = plus_one(d, x);
            let left = phi(d, s, shifted);
            let inner = phi(d, s, x);
            let right = d.apply(s.up, &[inner]);
            d.eq_at(u_lvl, s.carrier, left, right)
        };
        let proof = int_cases(
            dev,
            &goal,
            &|d, n| {
                let inner = uiter(d, s, n);
                let target = d.apply(s.up, &[inner]);
                d.refl_at(u_lvl, s.carrier, target)
            },
            &|d, n| {
                // `negSucc m + 1` only reduces once `m` is a constructor, so
                // split it; both branches are `symm (h (down^m e))`.
                d.induct(
                    &|d2, m| {
                        let value = neg_succ(d2, m);
                        goal(d2, value)
                    },
                    &|d2| {
                        let zero = d2.zero();
                        let base = diter(d2, s, zero);
                        let stepped = {
                            let inner = d2.apply(s.down, &[base]);
                            d2.apply(s.up, &[inner])
                        };
                        let witness = d2.apply(h, &[base]);
                        d2.symm_at(u_lvl, s.carrier, stepped, base, witness)
                    },
                    &|d2, k, _ih| {
                        let succ_k = d2.succ(k);
                        let base = diter(d2, s, succ_k);
                        let stepped = {
                            let inner = d2.apply(s.down, &[base]);
                            d2.apply(s.up, &[inner])
                        };
                        let witness = d2.apply(h, &[base]);
                        d2.symm_at(u_lvl, s.carrier, stepped, base, witness)
                    },
                    n,
                )
            },
            t,
        );

        let mut binders = head.binders.to_vec();
        binders.push((h_fv, hypothesis_ty));
        binders.push((t_fv, int_ty));
        let conclusion = goal(dev, t);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, proof);
        dev.declare_theorem_u(names.iter_succ, vec![names.uparam], statement, value)?;
    }

    // ---- iter (t−1) = down (iter t) -----------------------------------------
    //
    // Mirror image: `negSucc` is definitional and the `ofNat` branch crosses
    // zero, so it needs `down ∘ up = id` — and one `subNatNat` rewrite, because
    // `1 − k` does not reduce for a variable `k`.
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let hypothesis_ty = if weaken == Weakening::IntIterPredDropInverse {
            true_ty
        } else {
            left_inverse_ty(dev, s)
        };
        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);
        let sub_nat_nat = dev.int_prelude().sub_nat_nat;
        let sub_nat_nat_succ_succ = dev.int_prelude().sub_nat_nat_succ_succ;
        let sub_nat_nat_zero = dev.int_prelude().sub_nat_nat_zero;

        let goal = |d: &mut CharDev<'_>, x: ExprId| {
            let shifted = minus_one(d, x);
            let left = phi(d, s, shifted);
            let inner = phi(d, s, x);
            let right = d.apply(s.down, &[inner]);
            d.eq_at(u_lvl, s.carrier, left, right)
        };
        let proof = int_cases(
            dev,
            &goal,
            &|d, n| {
                d.induct(
                    &|d2, m| {
                        let value = of_nat(d2, m);
                        goal(d2, value)
                    },
                    &|d2| {
                        // `ofNat 0 − 1 ≡ negSucc 0`, so both sides are `down e`.
                        let target = d2.apply(s.down, &[s.point]);
                        d2.refl_at(u_lvl, s.carrier, target)
                    },
                    &|d2, k, _ih| {
                        // `ofNat (k+1) − 1 ≡ subNatNat (k+1) 1 = subNatNat k 0 = ofNat k`.
                        let zero = d2.zero();
                        let succ_k = d2.succ(k);
                        let succ_zero = d2.succ(zero);
                        let big = d2.const_app(sub_nat_nat, &[succ_k, succ_zero]);
                        let small = d2.const_app(sub_nat_nat, &[k, zero]);
                        let target = of_nat(d2, k);
                        let step_one = d2.const_app(sub_nat_nat_succ_succ, &[k, zero]);
                        let step_two = d2.const_app(sub_nat_nat_zero, &[k]);
                        let collapsed =
                            d2.trans_at(one_lvl, int_ty, big, small, target, step_one, step_two);
                        let lifted = d2.congr_at(
                            one_lvl,
                            int_ty,
                            u_lvl,
                            s.carrier,
                            big,
                            target,
                            collapsed,
                            &|d3, x| phi(d3, s, x),
                        );
                        let iterated = uiter(d2, s, k);
                        let stepped = {
                            let inner = d2.apply(s.up, &[iterated]);
                            d2.apply(s.down, &[inner])
                        };
                        let witness = d2.apply(h, &[iterated]);
                        let flipped = d2.symm_at(u_lvl, s.carrier, stepped, iterated, witness);
                        let start = phi(d2, s, big);
                        d2.trans_at(u_lvl, s.carrier, start, iterated, stepped, lifted, flipped)
                    },
                    n,
                )
            },
            &|d, n| {
                let succ_n = d.succ(n);
                let inner = diter(d, s, succ_n);
                let target = d.apply(s.down, &[inner]);
                d.refl_at(u_lvl, s.carrier, target)
            },
            t,
        );

        let mut binders = head.binders.to_vec();
        binders.push((h_fv, hypothesis_ty));
        binders.push((t_fv, int_ty));
        let conclusion = goal(dev, t);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, proof);
        dev.declare_theorem_u(names.iter_pred, vec![names.uparam], statement, value)?;
    }

    // ---- up is injective -----------------------------------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let hypothesis_ty = left_inverse_ty(dev, s);
        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);
        let x_fv = dev.fresh_fvar();
        let x = dev.kernel().fvar(x_fv);
        let y_fv = dev.fresh_fvar();
        let y = dev.kernel().fvar(y_fv);
        let up_x = dev.apply(s.up, &[x]);
        let up_y = dev.apply(s.up, &[y]);
        let equation_ty = dev.eq_at(u_lvl, s.carrier, up_x, up_y);
        let eq_fv = dev.fresh_fvar();
        let eq = dev.kernel().fvar(eq_fv);

        let down_up_x = dev.apply(s.down, &[up_x]);
        let down_up_y = dev.apply(s.down, &[up_y]);
        let lifted = dev.congr_at(
            u_lvl,
            s.carrier,
            u_lvl,
            s.carrier,
            up_x,
            up_y,
            eq,
            &|d, z| d.apply(s.down, &[z]),
        );
        let hx = dev.apply(h, &[x]);
        let hy = dev.apply(h, &[y]);
        let start = dev.symm_at(u_lvl, s.carrier, down_up_x, x, hx);
        let middle = dev.trans_at(u_lvl, s.carrier, x, down_up_x, down_up_y, start, lifted);
        let body = dev.trans_at(u_lvl, s.carrier, x, down_up_y, y, middle, hy);

        let mut binders = head.binders.to_vec();
        binders.push((h_fv, hypothesis_ty));
        binders.push((x_fv, s.carrier));
        binders.push((y_fv, s.carrier));
        binders.push((eq_fv, equation_ty));
        let conclusion = dev.eq_at(u_lvl, s.carrier, x, y);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.up_injective, vec![names.uparam], statement, value)?;
    }

    // ---- the up-iterates of e are pairwise distinct --------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let inverse_ty = if weaken == Weakening::IntIterUpInjectiveDropInverse {
            true_ty
        } else {
            left_inverse_ty(dev, s)
        };
        let aperiodic = if weaken == Weakening::IntIterUpInjectiveDropAperiodicity {
            true_ty
        } else {
            aperiodic_ty(dev, s)
        };
        let hinv_fv = dev.fresh_fvar();
        let hinv = dev.kernel().fvar(hinv_fv);
        let haper_fv = dev.fresh_fvar();
        let haper = dev.kernel().fvar(haper_fv);
        let a_fv = dev.fresh_fvar();
        let a = dev.kernel().fvar(a_fv);
        let b_fv = dev.fresh_fvar();
        let b = dev.kernel().fvar(b_fv);
        let left = uiter(dev, s, a);
        let right = uiter(dev, s, b);
        let equation_ty = dev.eq_at(u_lvl, s.carrier, left, right);
        let eq_fv = dev.fresh_fvar();
        let eq = dev.kernel().fvar(eq_fv);

        let cancel = {
            let cst = dev.kernel().const_(names.up_injective, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hinv])
        };

        let statement_at = |d: &mut CharDev<'_>, i: ExprId, j: ExprId| {
            let left = uiter(d, s, i);
            let right = uiter(d, s, j);
            let hypothesis = d.eq_at(u_lvl, s.carrier, left, right);
            let conclusion = d.eq(i, j);
            d.arrow(hypothesis, conclusion)
        };
        let motive = |d: &mut CharDev<'_>, i: ExprId| {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = statement_at(d, i, j);
            let nat = d.nat_ty();
            d.pi_fv(j_fv, nat, body)
        };
        let at_point = |d: &mut CharDev<'_>, i: ExprId, predecessor: Option<(ExprId, ExprId)>| {
            let nat = d.nat_ty();
            let zero = d.zero();
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let inner = d.induct(
                &|d2, x| statement_at(d2, i, x),
                &|d2| {
                    let hyp_ty = {
                        let left = uiter(d2, s, i);
                        let right = uiter(d2, s, zero);
                        d2.eq_at(u_lvl, s.carrier, left, right)
                    };
                    let h_fv = d2.fresh_fvar();
                    let hypothesis = d2.kernel().fvar(h_fv);
                    let body = if let Some((p, _)) = predecessor {
                        // `up^(p+1) e = e` is aperiodicity, flipped.
                        let target = d2.eq(i, zero);
                        let left = uiter(d2, s, i);
                        let right = uiter(d2, s, zero);
                        let flipped = d2.symm_at(u_lvl, s.carrier, left, right, hypothesis);
                        let contradiction = d2.apply(haper, &[p, flipped]);
                        d2.absurd(target, contradiction)
                    } else {
                        d2.refl(zero)
                    };
                    d2.lam_fv(h_fv, hyp_ty, body)
                },
                &|d2, jj, _inner_ih| {
                    let succ_j = d2.succ(jj);
                    let hyp_ty = {
                        let left = uiter(d2, s, i);
                        let right = uiter(d2, s, succ_j);
                        d2.eq_at(u_lvl, s.carrier, left, right)
                    };
                    let h_fv = d2.fresh_fvar();
                    let hypothesis = d2.kernel().fvar(h_fv);
                    let body = if let Some((p, ih)) = predecessor {
                        let iter_p = uiter(d2, s, p);
                        let iter_j = uiter(d2, s, jj);
                        let stripped = d2.apply(cancel, &[iter_p, iter_j, hypothesis]);
                        let equal = d2.apply(ih, &[jj, stripped]);
                        d2.congr(p, jj, equal, &|d3, x| d3.succ(x))
                    } else {
                        let target = d2.eq(zero, succ_j);
                        let contradiction = d2.apply(haper, &[jj, hypothesis]);
                        d2.absurd(target, contradiction)
                    };
                    d2.lam_fv(h_fv, hyp_ty, body)
                },
                j,
            );
            d.lam_fv(j_fv, nat, inner)
        };
        let zero = dev.zero();
        let proof = dev.induct(
            &motive,
            &|d| at_point(d, zero, None),
            &|d, i, ih| {
                let succ_i = d.succ(i);
                at_point(d, succ_i, Some((i, ih)))
            },
            a,
        );
        let applied = dev.apply(proof, &[b, eq]);

        let mut binders = head.binders.to_vec();
        binders.push((hinv_fv, inverse_ty));
        binders.push((haper_fv, aperiodic));
        binders.push((a_fv, nat_ty));
        binders.push((b_fv, nat_ty));
        binders.push((eq_fv, equation_ty));
        let conclusion = dev.eq(a, b);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, applied);
        dev.declare_theorem_u(
            names.iter_up_injective,
            vec![names.uparam],
            statement,
            value,
        )?;
    }

    // ---- up (down^(n+1) e) = down^n e ---------------------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let hypothesis_ty = if weaken == Weakening::IntShiftDropInverse {
            true_ty
        } else {
            right_inverse_ty(dev, s)
        };
        let h_fv = dev.fresh_fvar();
        let h = dev.kernel().fvar(h_fv);
        let n_fv = dev.fresh_fvar();
        let n = dev.kernel().fvar(n_fv);
        let succ_n = dev.succ(n);
        let deep = diter(dev, s, succ_n);
        let lifted = dev.apply(s.up, &[deep]);
        let shallow = diter(dev, s, n);
        let equation = dev.eq_at(u_lvl, s.carrier, lifted, shallow);
        let mut binders = head.binders.to_vec();
        binders.push((h_fv, hypothesis_ty));
        binders.push((n_fv, nat_ty));
        let statement = dev.close_pi(&binders, equation);
        let body = dev.apply(h, &[shallow]);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.shift, vec![names.uparam], statement, value)?;
    }

    // ---- an up-iterate is never a down-iterate, unless both are e ------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let inverse_ty = if weaken == Weakening::IntCrossDropInverse {
            true_ty
        } else {
            right_inverse_ty(dev, s)
        };
        let aperiodic = if weaken == Weakening::IntCrossDropAperiodicity {
            true_ty
        } else {
            aperiodic_ty(dev, s)
        };
        let hinv_fv = dev.fresh_fvar();
        let hinv = dev.kernel().fvar(hinv_fv);
        let haper_fv = dev.fresh_fvar();
        let haper = dev.kernel().fvar(haper_fv);
        let b_fv = dev.fresh_fvar();
        let b = dev.kernel().fvar(b_fv);
        let a_fv = dev.fresh_fvar();
        let a = dev.kernel().fvar(a_fv);

        let shift_at = {
            let cst = dev.kernel().const_(names.shift, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hinv])
        };
        let zero_ne_succ = dev.kernel().const_(nat.zero_ne_succ, vec![]);

        let conclusion_at = |d: &mut CharDev<'_>, i: ExprId, j: ExprId| {
            let zero = d.zero();
            let left = d.eq(i, zero);
            let right = d.eq(j, zero);
            d.and_of(left, right)
        };
        let statement_at = |d: &mut CharDev<'_>, i: ExprId, j: ExprId| {
            let left = uiter(d, s, i);
            let right = diter(d, s, j);
            let hypothesis = d.eq_at(u_lvl, s.carrier, left, right);
            let conclusion = conclusion_at(d, i, j);
            d.arrow(hypothesis, conclusion)
        };
        let motive = |d: &mut CharDev<'_>, j: ExprId| {
            let i_fv = d.fresh_fvar();
            let i = d.kernel().fvar(i_fv);
            let body = statement_at(d, i, j);
            let nat = d.nat_ty();
            d.pi_fv(i_fv, nat, body)
        };
        let zero = dev.zero();
        let proof = dev.induct(
            &motive,
            &|d| {
                // `up^a e = e`: possible only at `a = 0`.
                let nat = d.nat_ty();
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let inner = d.induct(
                    &|d2, x| statement_at(d2, x, zero),
                    &|d2| {
                        let hyp_ty = {
                            let left = uiter(d2, s, zero);
                            let right = diter(d2, s, zero);
                            d2.eq_at(u_lvl, s.carrier, left, right)
                        };
                        let h_fv = d2.fresh_fvar();
                        let left = d2.eq(zero, zero);
                        let right = d2.eq(zero, zero);
                        let proof_left = d2.refl(zero);
                        let proof_right = d2.refl(zero);
                        let body = d2.and_intro(left, right, proof_left, proof_right);
                        d2.lam_fv(h_fv, hyp_ty, body)
                    },
                    &|d2, k, _ih| {
                        let succ_k = d2.succ(k);
                        let hyp_ty = {
                            let left = uiter(d2, s, succ_k);
                            let right = diter(d2, s, zero);
                            d2.eq_at(u_lvl, s.carrier, left, right)
                        };
                        let h_fv = d2.fresh_fvar();
                        let hypothesis = d2.kernel().fvar(h_fv);
                        let left = uiter(d2, s, succ_k);
                        let right = diter(d2, s, zero);
                        let flipped = d2.symm_at(u_lvl, s.carrier, left, right, hypothesis);
                        let contradiction = d2.apply(haper, &[k, flipped]);
                        let target = conclusion_at(d2, succ_k, zero);
                        let body = d2.absurd(target, contradiction);
                        d2.lam_fv(h_fv, hyp_ty, body)
                    },
                    i,
                );
                d.lam_fv(i_fv, nat, inner)
            },
            &|d, m, ih| {
                // `up^a e = down^(m+1) e` gives `up^(a+1) e = down^m e`, and the
                // induction hypothesis then demands `a+1 = 0`.
                let nat = d.nat_ty();
                let succ_m = d.succ(m);
                let i_fv = d.fresh_fvar();
                let i = d.kernel().fvar(i_fv);
                let hyp_ty = {
                    let left = uiter(d, s, i);
                    let right = diter(d, s, succ_m);
                    d.eq_at(u_lvl, s.carrier, left, right)
                };
                let h_fv = d.fresh_fvar();
                let hypothesis = d.kernel().fvar(h_fv);
                let left = uiter(d, s, i);
                let right = diter(d, s, succ_m);
                let lifted = d.congr_at(
                    u_lvl,
                    s.carrier,
                    u_lvl,
                    s.carrier,
                    left,
                    right,
                    hypothesis,
                    &|d2, z| d2.apply(s.up, &[z]),
                );
                let up_left = d.apply(s.up, &[left]);
                let up_right = d.apply(s.up, &[right]);
                let shallow = diter(d, s, m);
                let stepped = d.apply(shift_at, &[m]);
                let chained = d.trans_at(
                    u_lvl, s.carrier, up_left, up_right, shallow, lifted, stepped,
                );
                let succ_i = d.succ(i);
                let recovered = d.apply(ih, &[succ_i, chained]);
                let zero = d.zero();
                let left_part = d.eq(succ_i, zero);
                let right_part = d.eq(m, zero);
                let projected = d.and_left(left_part, right_part, recovered);
                let flipped = d.symm(succ_i, zero, projected);
                let contradiction = d.apply(zero_ne_succ, &[i, flipped]);
                let target = conclusion_at(d, i, succ_m);
                let body = d.absurd(target, contradiction);
                let with_h = d.lam_fv(h_fv, hyp_ty, body);
                d.lam_fv(i_fv, nat, with_h)
            },
            b,
        );
        let applied = dev.apply(proof, &[a]);

        let mut binders = head.binders.to_vec();
        binders.push((hinv_fv, inverse_ty));
        binders.push((haper_fv, aperiodic));
        binders.push((b_fv, nat_ty));
        binders.push((a_fv, nat_ty));
        let conclusion = statement_at(dev, a, b);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, applied);
        dev.declare_theorem_u(names.cross, vec![names.uparam], statement, value)?;
    }

    // ---- the down-iterates of e are pairwise distinct ------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let inverse_ty = right_inverse_ty(dev, s);
        let aperiodic = if weaken == Weakening::IntDownInjectiveDropAperiodicity {
            true_ty
        } else {
            aperiodic_ty(dev, s)
        };
        let hinv_fv = dev.fresh_fvar();
        let hinv = dev.kernel().fvar(hinv_fv);
        let haper_fv = dev.fresh_fvar();
        let haper = dev.kernel().fvar(haper_fv);
        let a_fv = dev.fresh_fvar();
        let a = dev.kernel().fvar(a_fv);
        let b_fv = dev.fresh_fvar();
        let b = dev.kernel().fvar(b_fv);
        let left = diter(dev, s, a);
        let right = diter(dev, s, b);
        let equation_ty = dev.eq_at(u_lvl, s.carrier, left, right);
        let eq_fv = dev.fresh_fvar();
        let eq = dev.kernel().fvar(eq_fv);

        let shift_at = {
            let cst = dev.kernel().const_(names.shift, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hinv])
        };
        let cross_at = {
            let cst = dev.kernel().const_(names.cross, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hinv, haper])
        };
        let zero_ne_succ = dev.kernel().const_(nat.zero_ne_succ, vec![]);

        let statement_at = |d: &mut CharDev<'_>, i: ExprId, j: ExprId| {
            let left = diter(d, s, i);
            let right = diter(d, s, j);
            let hypothesis = d.eq_at(u_lvl, s.carrier, left, right);
            let conclusion = d.eq(i, j);
            d.arrow(hypothesis, conclusion)
        };
        let motive = |d: &mut CharDev<'_>, i: ExprId| {
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let body = statement_at(d, i, j);
            let nat = d.nat_ty();
            d.pi_fv(j_fv, nat, body)
        };
        // `down^i e = e` (either orientation) contradicts `cross`, whose second
        // component says the down-exponent is zero.
        let refute = |d: &mut CharDev<'_>, k: ExprId, equation: ExprId, target: ExprId| {
            let zero = d.zero();
            let succ_k = d.succ(k);
            let recovered = d.apply(cross_at, &[succ_k, zero, equation]);
            let left_part = d.eq(zero, zero);
            let right_part = d.eq(succ_k, zero);
            let projected = d.and_right(left_part, right_part, recovered);
            let flipped = d.symm(succ_k, zero, projected);
            let contradiction = d.apply(zero_ne_succ, &[k, flipped]);
            d.absurd(target, contradiction)
        };
        let at_point = |d: &mut CharDev<'_>, i: ExprId, predecessor: Option<(ExprId, ExprId)>| {
            let nat = d.nat_ty();
            let zero = d.zero();
            let j_fv = d.fresh_fvar();
            let j = d.kernel().fvar(j_fv);
            let inner = d.induct(
                &|d2, x| statement_at(d2, i, x),
                &|d2| {
                    let hyp_ty = {
                        let left = diter(d2, s, i);
                        let right = diter(d2, s, zero);
                        d2.eq_at(u_lvl, s.carrier, left, right)
                    };
                    let h_fv = d2.fresh_fvar();
                    let hypothesis = d2.kernel().fvar(h_fv);
                    let body = if let Some((p, _)) = predecessor {
                        let left = diter(d2, s, i);
                        let right = diter(d2, s, zero);
                        let flipped = d2.symm_at(u_lvl, s.carrier, left, right, hypothesis);
                        let target = d2.eq(i, zero);
                        refute(d2, p, flipped, target)
                    } else {
                        d2.refl(zero)
                    };
                    d2.lam_fv(h_fv, hyp_ty, body)
                },
                &|d2, jj, _inner_ih| {
                    let succ_j = d2.succ(jj);
                    let hyp_ty = {
                        let left = diter(d2, s, i);
                        let right = diter(d2, s, succ_j);
                        d2.eq_at(u_lvl, s.carrier, left, right)
                    };
                    let h_fv = d2.fresh_fvar();
                    let hypothesis = d2.kernel().fvar(h_fv);
                    let body = if let Some((p, ih)) = predecessor {
                        // Both sides are `down`-steps: apply `up` and cancel.
                        let left = diter(d2, s, i);
                        let right = diter(d2, s, succ_j);
                        let lifted = d2.congr_at(
                            u_lvl,
                            s.carrier,
                            u_lvl,
                            s.carrier,
                            left,
                            right,
                            hypothesis,
                            &|d3, z| d3.apply(s.up, &[z]),
                        );
                        let up_left = d2.apply(s.up, &[left]);
                        let up_right = d2.apply(s.up, &[right]);
                        let shallow_left = diter(d2, s, p);
                        let shallow_right = diter(d2, s, jj);
                        let step_left = d2.apply(shift_at, &[p]);
                        let step_right = d2.apply(shift_at, &[jj]);
                        let opened = d2.symm_at(u_lvl, s.carrier, up_left, shallow_left, step_left);
                        let joined = d2.trans_at(
                            u_lvl,
                            s.carrier,
                            shallow_left,
                            up_left,
                            up_right,
                            opened,
                            lifted,
                        );
                        let stripped = d2.trans_at(
                            u_lvl,
                            s.carrier,
                            shallow_left,
                            up_right,
                            shallow_right,
                            joined,
                            step_right,
                        );
                        let equal = d2.apply(ih, &[jj, stripped]);
                        d2.congr(p, jj, equal, &|d3, x| d3.succ(x))
                    } else {
                        let target = d2.eq(zero, succ_j);
                        refute(d2, jj, hypothesis, target)
                    };
                    d2.lam_fv(h_fv, hyp_ty, body)
                },
                j,
            );
            d.lam_fv(j_fv, nat, inner)
        };
        let zero = dev.zero();
        let proof = dev.induct(
            &motive,
            &|d| at_point(d, zero, None),
            &|d, i, ih| {
                let succ_i = d.succ(i);
                at_point(d, succ_i, Some((i, ih)))
            },
            a,
        );
        let applied = dev.apply(proof, &[b, eq]);

        let mut binders = head.binders.to_vec();
        binders.push((hinv_fv, inverse_ty));
        binders.push((haper_fv, aperiodic));
        binders.push((a_fv, nat_ty));
        binders.push((b_fv, nat_ty));
        binders.push((eq_fv, equation_ty));
        let conclusion = dev.eq(a, b);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, applied);
        dev.declare_theorem_u(
            names.iter_down_injective,
            vec![names.uparam],
            statement,
            value,
        )?;
    }

    // ---- the comparison map is injective ------------------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let left_ty = if weaken == Weakening::IntInjectiveDropRetraction {
            true_ty
        } else {
            left_inverse_ty(dev, s)
        };
        let right_ty = right_inverse_ty(dev, s);
        let aperiodic = if weaken == Weakening::IntInjectiveDropAperiodicity {
            true_ty
        } else {
            aperiodic_ty(dev, s)
        };
        let hleft_fv = dev.fresh_fvar();
        let hleft = dev.kernel().fvar(hleft_fv);
        let hright_fv = dev.fresh_fvar();
        let hright = dev.kernel().fvar(hright_fv);
        let haper_fv = dev.fresh_fvar();
        let haper = dev.kernel().fvar(haper_fv);
        let s_fv = dev.fresh_fvar();
        let source = dev.kernel().fvar(s_fv);
        let t_fv = dev.fresh_fvar();
        let target_int = dev.kernel().fvar(t_fv);
        let phi_source = phi(dev, s, source);
        let phi_target = phi(dev, s, target_int);
        let equation_ty = dev.eq_at(u_lvl, s.carrier, phi_source, phi_target);
        let eq_fv = dev.fresh_fvar();
        let eq = dev.kernel().fvar(eq_fv);

        let up_inj = {
            let cst = dev.kernel().const_(names.iter_up_injective, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hleft, haper])
        };
        let down_inj = {
            let cst = dev.kernel().const_(names.iter_down_injective, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hright, haper])
        };
        let cross_at = {
            let cst = dev.kernel().const_(names.cross, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hright, haper])
        };
        let zero_ne_succ = dev.kernel().const_(nat.zero_ne_succ, vec![]);
        let succ_injective = dev.kernel().const_(nat.succ_injective, vec![]);

        let statement_at = |d: &mut CharDev<'_>, x: ExprId, y: ExprId| {
            let left = phi(d, s, x);
            let right = phi(d, s, y);
            let hypothesis = d.eq_at(u_lvl, s.carrier, left, right);
            let conclusion = d.eq_at(one_lvl, int_ty, x, y);
            d.arrow(hypothesis, conclusion)
        };
        // A crossing equation `up^a e = down^(b+1) e` is impossible: `cross`
        // forces the down-exponent to be zero.
        let refute_cross =
            |d: &mut CharDev<'_>, a: ExprId, b: ExprId, equation: ExprId, target: ExprId| {
                let zero = d.zero();
                let succ_b = d.succ(b);
                let recovered = d.apply(cross_at, &[succ_b, a, equation]);
                let left_part = d.eq(a, zero);
                let right_part = d.eq(succ_b, zero);
                let projected = d.and_right(left_part, right_part, recovered);
                let flipped = d.symm(succ_b, zero, projected);
                let contradiction = d.apply(zero_ne_succ, &[b, flipped]);
                d.absurd(target, contradiction)
            };
        let proof = int_cases(
            dev,
            &|d, x| {
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let body = statement_at(d, x, y);
                let int_ty = d.int_ty();
                d.pi_fv(y_fv, int_ty, body)
            },
            &|d, a| {
                let source_value = of_nat(d, a);
                let int_ty = d.int_ty();
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let inner = int_cases(
                    d,
                    &|d2, yy| statement_at(d2, source_value, yy),
                    &|d2, b| {
                        let target_value = of_nat(d2, b);
                        let hyp_ty = {
                            let left = phi(d2, s, source_value);
                            let right = phi(d2, s, target_value);
                            d2.eq_at(u_lvl, s.carrier, left, right)
                        };
                        let h_fv = d2.fresh_fvar();
                        let hypothesis = d2.kernel().fvar(h_fv);
                        let equal = d2.apply(up_inj, &[a, b, hypothesis]);
                        let nat = d2.nat_ty();
                        let int_ty = d2.int_ty();
                        let body =
                            d2.congr_at(one_lvl, nat, one_lvl, int_ty, a, b, equal, &|d3, x| {
                                of_nat(d3, x)
                            });
                        d2.lam_fv(h_fv, hyp_ty, body)
                    },
                    &|d2, b| {
                        let target_value = neg_succ(d2, b);
                        let hyp_ty = {
                            let left = phi(d2, s, source_value);
                            let right = phi(d2, s, target_value);
                            d2.eq_at(u_lvl, s.carrier, left, right)
                        };
                        let h_fv = d2.fresh_fvar();
                        let hypothesis = d2.kernel().fvar(h_fv);
                        let target = d2.eq_at(one_lvl, int_ty, source_value, target_value);
                        let body = refute_cross(d2, a, b, hypothesis, target);
                        d2.lam_fv(h_fv, hyp_ty, body)
                    },
                    y,
                );
                d.lam_fv(y_fv, int_ty, inner)
            },
            &|d, a| {
                let source_value = neg_succ(d, a);
                let int_ty = d.int_ty();
                let y_fv = d.fresh_fvar();
                let y = d.kernel().fvar(y_fv);
                let inner = int_cases(
                    d,
                    &|d2, yy| statement_at(d2, source_value, yy),
                    &|d2, b| {
                        let target_value = of_nat(d2, b);
                        let hyp_ty = {
                            let left = phi(d2, s, source_value);
                            let right = phi(d2, s, target_value);
                            d2.eq_at(u_lvl, s.carrier, left, right)
                        };
                        let h_fv = d2.fresh_fvar();
                        let hypothesis = d2.kernel().fvar(h_fv);
                        let left = phi(d2, s, source_value);
                        let right = phi(d2, s, target_value);
                        let flipped = d2.symm_at(u_lvl, s.carrier, left, right, hypothesis);
                        let target = d2.eq_at(one_lvl, int_ty, source_value, target_value);
                        let body = refute_cross(d2, b, a, flipped, target);
                        d2.lam_fv(h_fv, hyp_ty, body)
                    },
                    &|d2, b| {
                        let target_value = neg_succ(d2, b);
                        let hyp_ty = {
                            let left = phi(d2, s, source_value);
                            let right = phi(d2, s, target_value);
                            d2.eq_at(u_lvl, s.carrier, left, right)
                        };
                        let h_fv = d2.fresh_fvar();
                        let hypothesis = d2.kernel().fvar(h_fv);
                        let succ_a = d2.succ(a);
                        let succ_b = d2.succ(b);
                        let equal = d2.apply(down_inj, &[succ_a, succ_b, hypothesis]);
                        let stripped = d2.apply(succ_injective, &[a, b, equal]);
                        let nat = d2.nat_ty();
                        let int_ty = d2.int_ty();
                        let body =
                            d2.congr_at(one_lvl, nat, one_lvl, int_ty, a, b, stripped, &|d3, x| {
                                neg_succ(d3, x)
                            });
                        d2.lam_fv(h_fv, hyp_ty, body)
                    },
                    y,
                );
                d.lam_fv(y_fv, int_ty, inner)
            },
            source,
        );
        let applied = dev.apply(proof, &[target_int, eq]);

        let mut binders = head.binders.to_vec();
        binders.push((hleft_fv, left_ty));
        binders.push((hright_fv, right_ty));
        binders.push((haper_fv, aperiodic));
        binders.push((s_fv, int_ty));
        binders.push((t_fv, int_ty));
        binders.push((eq_fv, equation_ty));
        let conclusion = dev.eq_at(one_lvl, int_ty, source, target_int);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, applied);
        dev.declare_theorem_u(names.injective, vec![names.uparam], statement, value)?;
    }

    // ---- the comparison map is surjective -----------------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let left_ty = left_inverse_ty(dev, s);
        let right_ty = right_inverse_ty(dev, s);
        let generation = if weaken == Weakening::IntSurjectiveDropGeneration {
            true_ty
        } else {
            generation_ty(dev, s)
        };
        let hleft_fv = dev.fresh_fvar();
        let hleft = dev.kernel().fvar(hleft_fv);
        let hright_fv = dev.fresh_fvar();
        let hright = dev.kernel().fvar(hright_fv);
        let hgen_fv = dev.fresh_fvar();
        let hgen = dev.kernel().fvar(hgen_fv);
        let y_fv = dev.fresh_fvar();
        let y = dev.kernel().fvar(y_fv);

        let succ_rule = {
            let cst = dev.kernel().const_(names.iter_succ, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hright])
        };
        let pred_rule = {
            let cst = dev.kernel().const_(names.iter_pred, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hleft])
        };

        let reachable_predicate = |d: &mut CharDev<'_>, target: ExprId| {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let applied = phi(d, s, t);
            let equation = d.eq_at(u_lvl, s.carrier, applied, target);
            let int_ty = d.int_ty();
            d.lam_fv(t_fv, int_ty, equation)
        };
        let reachable_prop = |d: &mut CharDev<'_>, target: ExprId| {
            let predicate = reachable_predicate(d, target);
            let int_ty = d.int_ty();
            d.exists_at(one_lvl, int_ty, predicate)
        };

        let motive = {
            let m_fv = dev.fresh_fvar();
            let m = dev.kernel().fvar(m_fv);
            let body = reachable_prop(dev, m);
            dev.lam_fv(m_fv, s.carrier, body)
        };
        let base = {
            let predicate = reachable_predicate(dev, s.point);
            let zero = izero(dev);
            let proof = dev.refl_at(u_lvl, s.carrier, s.point);
            dev.exists_intro_at(one_lvl, int_ty, predicate, zero, proof)
        };
        let shift_step = |d: &mut CharDev<'_>, endo: ExprId, rule: ExprId, upward: bool| {
            let m_fv = d.fresh_fvar();
            let m = d.kernel().fvar(m_fv);
            let ih_ty = reachable_prop(d, m);
            let shifted_point = d.apply(endo, &[m]);
            let target = reachable_prop(d, shifted_point);
            let predicate_m = reachable_predicate(d, m);
            let predicate_shifted = reachable_predicate(d, shifted_point);
            let minor = {
                let t_fv = d.fresh_fvar();
                let t = d.kernel().fvar(t_fv);
                let applied = phi(d, s, t);
                let ht_ty = d.eq_at(u_lvl, s.carrier, applied, m);
                let ht_fv = d.fresh_fvar();
                let ht = d.kernel().fvar(ht_fv);
                let witness = if upward {
                    plus_one(d, t)
                } else {
                    minus_one(d, t)
                };
                let shifted_iter = phi(d, s, witness);
                let stepped = d.apply(endo, &[applied]);
                let first = d.apply(rule, &[t]);
                let second = d.congr_at(
                    u_lvl,
                    s.carrier,
                    u_lvl,
                    s.carrier,
                    applied,
                    m,
                    ht,
                    &|d2, z| d2.apply(endo, &[z]),
                );
                let proof = d.trans_at(
                    u_lvl,
                    s.carrier,
                    shifted_iter,
                    stepped,
                    shifted_point,
                    first,
                    second,
                );
                let witnessed =
                    d.exists_intro_at(one_lvl, int_ty, predicate_shifted, witness, proof);
                let inner = d.lam_fv(ht_fv, ht_ty, witnessed);
                d.lam_fv(t_fv, int_ty, inner)
            };
            let ih_fv = d.fresh_fvar();
            let ih = d.kernel().fvar(ih_fv);
            let eliminated = d.exists_elim_at(one_lvl, int_ty, predicate_m, target, minor, ih);
            let inner = d.lam_fv(ih_fv, ih_ty, eliminated);
            d.lam_fv(m_fv, s.carrier, inner)
        };
        let up_step = shift_step(dev, s.up, succ_rule, true);
        let down_step = shift_step(dev, s.down, pred_rule, false);
        let body = dev.apply(hgen, &[motive, base, up_step, down_step, y]);

        let mut binders = head.binders.to_vec();
        binders.push((hleft_fv, left_ty));
        binders.push((hright_fv, right_ty));
        binders.push((hgen_fv, generation));
        binders.push((y_fv, s.carrier));
        let conclusion = reachable_prop(dev, y);
        let statement = dev.close_pi(&binders, conclusion);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.surjective, vec![names.uparam], statement, value)?;
    }

    // ---- the packaged categoricity statement --------------------------------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let left_ty = left_inverse_ty(dev, s);
        let right_ty = right_inverse_ty(dev, s);
        let generation = generation_ty(dev, s);
        let aperiodic = aperiodic_ty(dev, s);
        let hleft_fv = dev.fresh_fvar();
        let hleft = dev.kernel().fvar(hleft_fv);
        let hright_fv = dev.fresh_fvar();
        let hright = dev.kernel().fvar(hright_fv);
        let hgen_fv = dev.fresh_fvar();
        let hgen = dev.kernel().fvar(hgen_fv);
        let haper_fv = dev.fresh_fvar();
        let haper = dev.kernel().fvar(haper_fv);

        let hom_zero = {
            let zero = izero(dev);
            let applied = phi(dev, s, zero);
            dev.eq_at(u_lvl, s.carrier, applied, s.point)
        };
        let hom_shift = |d: &mut CharDev<'_>, endo: ExprId, upward: bool| {
            let t_fv = d.fresh_fvar();
            let t = d.kernel().fvar(t_fv);
            let shifted = if upward {
                plus_one(d, t)
            } else {
                minus_one(d, t)
            };
            let left = phi(d, s, shifted);
            let inner = phi(d, s, t);
            let right = d.apply(endo, &[inner]);
            let body = d.eq_at(u_lvl, s.carrier, left, right);
            let int_ty = d.int_ty();
            d.pi_fv(t_fv, int_ty, body)
        };
        let hom_succ = hom_shift(dev, s.up, true);
        let hom_pred = hom_shift(dev, s.down, false);
        let shifts = dev.and_of(hom_succ, hom_pred);
        let preserves = dev.and_of(hom_zero, shifts);

        let injective_tail = {
            let x_fv = dev.fresh_fvar();
            let x = dev.kernel().fvar(x_fv);
            let y_fv = dev.fresh_fvar();
            let y = dev.kernel().fvar(y_fv);
            let left = phi(dev, s, x);
            let right = phi(dev, s, y);
            let hypothesis = dev.eq_at(u_lvl, s.carrier, left, right);
            let conclusion = dev.eq_at(one_lvl, int_ty, x, y);
            let body = dev.arrow(hypothesis, conclusion);
            dev.close_pi(&[(x_fv, int_ty), (y_fv, int_ty)], body)
        };
        let surjective_tail = {
            let y_fv = dev.fresh_fvar();
            let y = dev.kernel().fvar(y_fv);
            let t_fv = dev.fresh_fvar();
            let t = dev.kernel().fvar(t_fv);
            let applied = phi(dev, s, t);
            let equation = dev.eq_at(u_lvl, s.carrier, applied, y);
            let predicate = dev.lam_fv(t_fv, int_ty, equation);
            let body = dev.exists_at(one_lvl, int_ty, predicate);
            dev.pi_fv(y_fv, s.carrier, body)
        };
        let bijective = dev.and_of(injective_tail, surjective_tail);
        let conclusion = dev.and_of(preserves, bijective);

        let mut binders = head.binders.to_vec();
        binders.push((hleft_fv, left_ty));
        binders.push((hright_fv, right_ty));
        binders.push((hgen_fv, generation));
        binders.push((haper_fv, aperiodic));
        let statement = dev.close_pi(&binders, conclusion);

        let hom_zero_proof = {
            let cst = dev.kernel().const_(names.iter_zero, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down])
        };
        let hom_succ_proof = {
            let cst = dev.kernel().const_(names.iter_succ, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hright])
        };
        let hom_pred_proof = {
            let cst = dev.kernel().const_(names.iter_pred, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hleft])
        };
        let shifts_proof = dev.and_intro(hom_succ, hom_pred, hom_succ_proof, hom_pred_proof);
        let preserves_proof = dev.and_intro(hom_zero, shifts, hom_zero_proof, shifts_proof);
        let injective_proof = {
            let cst = dev.kernel().const_(names.injective, vec![u_lvl]);
            dev.apply(
                cst,
                &[s.carrier, s.point, s.up, s.down, hleft, hright, haper],
            )
        };
        let surjective_proof = {
            let cst = dev.kernel().const_(names.surjective, vec![u_lvl]);
            dev.apply(
                cst,
                &[s.carrier, s.point, s.up, s.down, hleft, hright, hgen],
            )
        };
        let bijective_proof = dev.and_intro(
            injective_tail,
            surjective_tail,
            injective_proof,
            surjective_proof,
        );
        let body = dev.and_intro(preserves, bijective, preserves_proof, bijective_proof);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.categorical, vec![names.uparam], statement, value)?;
    }

    // ---- any structure-preserving map back is a two-sided inverse -----------
    {
        let head = fresh_head(dev, u_lvl, sort_u, nat_iter, names.iter);
        let s = head.s;
        let left_ty = left_inverse_ty(dev, s);
        let right_ty = right_inverse_ty(dev, s);
        let generation = if weaken == Weakening::IntIsoDropGeneration {
            true_ty
        } else {
            generation_ty(dev, s)
        };
        let hleft_fv = dev.fresh_fvar();
        let hleft = dev.kernel().fvar(hleft_fv);
        let hright_fv = dev.fresh_fvar();
        let hright = dev.kernel().fvar(hright_fv);
        let hgen_fv = dev.fresh_fvar();
        let hgen = dev.kernel().fvar(hgen_fv);

        let back_ty = dev.arrow(s.carrier, int_ty);
        let psi_fv = dev.fresh_fvar();
        let psi = dev.kernel().fvar(psi_fv);
        let base_ty = {
            let applied = dev.apply(psi, &[s.point]);
            let zero = izero(dev);
            let equation = dev.eq_at(one_lvl, int_ty, applied, zero);
            if weaken == Weakening::IntIsoDropBasePoint {
                true_ty
            } else {
                equation
            }
        };
        let recurrence_ty = |d: &mut CharDev<'_>, endo: ExprId, upward: bool| {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let shifted_point = d.apply(endo, &[x]);
            let left = d.apply(psi, &[shifted_point]);
            let inner = d.apply(psi, &[x]);
            let right = if upward {
                plus_one(d, inner)
            } else {
                minus_one(d, inner)
            };
            let body = d.eq_at(one_lvl, int_ty, left, right);
            d.pi_fv(x_fv, s.carrier, body)
        };
        let up_rule_ty = recurrence_ty(dev, s.up, true);
        let down_rule_ty = recurrence_ty(dev, s.down, false);
        let hbase_fv = dev.fresh_fvar();
        let hbase = dev.kernel().fvar(hbase_fv);
        let hup_fv = dev.fresh_fvar();
        let hup = dev.kernel().fvar(hup_fv);
        let hdown_fv = dev.fresh_fvar();
        let hdown = dev.kernel().fvar(hdown_fv);

        let succ_rule = {
            let cst = dev.kernel().const_(names.iter_succ, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hright])
        };
        let pred_rule = {
            let cst = dev.kernel().const_(names.iter_pred, vec![u_lvl]);
            dev.apply(cst, &[s.carrier, s.point, s.up, s.down, hleft])
        };

        // `iter ∘ psi = id_R`, by generation on `R`.
        let carrier_side = {
            let motive = {
                let x_fv = dev.fresh_fvar();
                let x = dev.kernel().fvar(x_fv);
                let applied = dev.apply(psi, &[x]);
                let mapped = phi(dev, s, applied);
                let body = dev.eq_at(u_lvl, s.carrier, mapped, x);
                dev.lam_fv(x_fv, s.carrier, body)
            };
            let base = {
                let applied = dev.apply(psi, &[s.point]);
                let zero = izero(dev);
                dev.congr_at(
                    one_lvl,
                    int_ty,
                    u_lvl,
                    s.carrier,
                    applied,
                    zero,
                    hbase,
                    &|d, z| phi(d, s, z),
                )
            };
            let step = |d: &mut CharDev<'_>,
                        endo: ExprId,
                        rule: ExprId,
                        psi_rule: ExprId,
                        upward: bool| {
                let x_fv = d.fresh_fvar();
                let x = d.kernel().fvar(x_fv);
                let psi_x = d.apply(psi, &[x]);
                let mapped = phi(d, s, psi_x);
                let ih_ty = d.eq_at(u_lvl, s.carrier, mapped, x);
                let ih_fv = d.fresh_fvar();
                let ih = d.kernel().fvar(ih_fv);
                let shifted_point = d.apply(endo, &[x]);
                let psi_shifted = d.apply(psi, &[shifted_point]);
                let shifted_int = if upward {
                    plus_one(d, psi_x)
                } else {
                    minus_one(d, psi_x)
                };
                let first = {
                    let witness = d.apply(psi_rule, &[x]);
                    d.congr_at(
                        one_lvl,
                        int_ty,
                        u_lvl,
                        s.carrier,
                        psi_shifted,
                        shifted_int,
                        witness,
                        &|d2, z| phi(d2, s, z),
                    )
                };
                let second = d.apply(rule, &[psi_x]);
                let third = d.congr_at(
                    u_lvl,
                    s.carrier,
                    u_lvl,
                    s.carrier,
                    mapped,
                    x,
                    ih,
                    &|d2, z| d2.apply(endo, &[z]),
                );
                let start = phi(d, s, psi_shifted);
                let middle = phi(d, s, shifted_int);
                let stepped = d.apply(endo, &[mapped]);
                let prefix = d.trans_at(u_lvl, s.carrier, start, middle, stepped, first, second);
                let body = d.trans_at(
                    u_lvl,
                    s.carrier,
                    start,
                    stepped,
                    shifted_point,
                    prefix,
                    third,
                );
                let inner = d.lam_fv(ih_fv, ih_ty, body);
                d.lam_fv(x_fv, s.carrier, inner)
            };
            let up_step = step(dev, s.up, succ_rule, hup, true);
            let down_step = step(dev, s.down, pred_rule, hdown, false);
            let x_fv = dev.fresh_fvar();
            let x = dev.kernel().fvar(x_fv);
            let applied = dev.apply(hgen, &[motive, base, up_step, down_step, x]);
            dev.lam_fv(x_fv, s.carrier, applied)
        };

        // `psi ∘ iter = id_Int`, by the uniqueness half already proved.
        let integer_side = {
            let composite = {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                let mapped = phi(dev, s, t);
                let body = dev.apply(psi, &[mapped]);
                dev.lam_fv(t_fv, int_ty, body)
            };
            let identity = {
                let t_fv = dev.fresh_fvar();
                let t = dev.kernel().fvar(t_fv);
                dev.lam_fv(t_fv, int_ty, t)
            };
            let shift_map = |d: &mut CharDev<'_>, upward: bool| {
                let t_fv = d.fresh_fvar();
                let t = d.kernel().fvar(t_fv);
                let body = if upward {
                    plus_one(d, t)
                } else {
                    minus_one(d, t)
                };
                let int_ty = d.int_ty();
                d.lam_fv(t_fv, int_ty, body)
            };
            let up_map = shift_map(dev, true);
            let down_map = shift_map(dev, false);
            let composite_rule = |d: &mut CharDev<'_>,
                                  rule: ExprId,
                                  psi_rule: ExprId,
                                  endo: ExprId,
                                  upward: bool| {
                let t_fv = d.fresh_fvar();
                let t = d.kernel().fvar(t_fv);
                let shifted = if upward {
                    plus_one(d, t)
                } else {
                    minus_one(d, t)
                };
                let mapped = phi(d, s, t);
                let mapped_shifted = phi(d, s, shifted);
                let stepped = d.apply(endo, &[mapped]);
                let first = {
                    let witness = d.apply(rule, &[t]);
                    d.congr_at(
                        u_lvl,
                        s.carrier,
                        one_lvl,
                        int_ty,
                        mapped_shifted,
                        stepped,
                        witness,
                        &|d2, z| d2.apply(psi, &[z]),
                    )
                };
                let second = d.apply(psi_rule, &[mapped]);
                let start = d.apply(psi, &[mapped_shifted]);
                let middle = d.apply(psi, &[stepped]);
                let inner = d.apply(psi, &[mapped]);
                let end = if upward {
                    plus_one(d, inner)
                } else {
                    minus_one(d, inner)
                };
                let body = d.trans_at(one_lvl, int_ty, start, middle, end, first, second);
                d.lam_fv(t_fv, int_ty, body)
            };
            let identity_rule = |d: &mut CharDev<'_>, upward: bool| {
                let t_fv = d.fresh_fvar();
                let t = d.kernel().fvar(t_fv);
                let shifted = if upward {
                    plus_one(d, t)
                } else {
                    minus_one(d, t)
                };
                let body = d.refl_at(one_lvl, int_ty, shifted);
                d.lam_fv(t_fv, int_ty, body)
            };
            let f_up = composite_rule(dev, succ_rule, hup, s.up, true);
            let f_down = composite_rule(dev, pred_rule, hdown, s.down, false);
            let g_up = identity_rule(dev, true);
            let g_down = identity_rule(dev, false);
            let t_fv = dev.fresh_fvar();
            let t = dev.kernel().fvar(t_fv);
            let cst = dev.kernel().const_(int.rec_unique, vec![one_lvl]);
            let applied = dev.apply(
                cst,
                &[
                    int_ty, composite, identity, up_map, down_map, hbase, f_up, g_up, f_down,
                    g_down, t,
                ],
            );
            dev.lam_fv(t_fv, int_ty, applied)
        };

        let carrier_claim = {
            let x_fv = dev.fresh_fvar();
            let x = dev.kernel().fvar(x_fv);
            let applied = dev.apply(psi, &[x]);
            let mapped = phi(dev, s, applied);
            let body = dev.eq_at(u_lvl, s.carrier, mapped, x);
            dev.pi_fv(x_fv, s.carrier, body)
        };
        let integer_claim = {
            let t_fv = dev.fresh_fvar();
            let t = dev.kernel().fvar(t_fv);
            let mapped = phi(dev, s, t);
            let applied = dev.apply(psi, &[mapped]);
            let body = dev.eq_at(one_lvl, int_ty, applied, t);
            dev.pi_fv(t_fv, int_ty, body)
        };
        let conclusion = dev.and_of(carrier_claim, integer_claim);

        let mut binders = head.binders.to_vec();
        binders.push((hleft_fv, left_ty));
        binders.push((hright_fv, right_ty));
        binders.push((hgen_fv, generation));
        binders.push((psi_fv, back_ty));
        binders.push((hbase_fv, base_ty));
        binders.push((hup_fv, up_rule_ty));
        binders.push((hdown_fv, down_rule_ty));
        let statement = dev.close_pi(&binders, conclusion);
        let body = dev.and_intro(carrier_claim, integer_claim, carrier_side, integer_side);
        let value = dev.close_lam(&binders, body);
        dev.declare_theorem_u(names.iso, vec![names.uparam], statement, value)?;
    }

    // ---- Int is itself such a structure: the non-vacuity witness ------------
    //
    // `up = (·+1)`, `down = (·−1)`. The two inverse laws are the ring laws, the
    // generation principle is `Int.Characterization.induction` verbatim, and
    // aperiodicity comes from `Nat.Peano.zero_ne_succ` through `Int.natAbs`.
    let int_up = {
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);
        let body = plus_one(dev, t);
        dev.lam_fv(t_fv, int_ty, body)
    };
    let int_down = {
        let t_fv = dev.fresh_fvar();
        let t = dev.kernel().fvar(t_fv);
        let body = minus_one(dev, t);
        dev.lam_fv(t_fv, int_ty, body)
    };

    {
        // `Nat.Peano.iter Int 0 (·+1) k = ofNat k`.
        let structure = Structure {
            level: one_lvl,
            nat_iter,
            iter: names.iter,
            carrier: int_ty,
            point: izero(dev),
            up: int_up,
            down: int_down,
        };
        let k_fv = dev.fresh_fvar();
        let k = dev.kernel().fvar(k_fv);
        let motive = |d: &mut CharDev<'_>, x: ExprId| {
            let left = uiter(d, structure, x);
            let right = of_nat(d, x);
            let int_ty = d.int_ty();
            d.eq_at(one_lvl, int_ty, left, right)
        };
        let proof = dev.induct(
            &motive,
            &|d| {
                let zero = izero(d);
                let int_ty = d.int_ty();
                d.refl_at(one_lvl, int_ty, zero)
            },
            &|d, j, ih| {
                let left = uiter(d, structure, j);
                let right = of_nat(d, j);
                let int_ty = d.int_ty();
                d.congr_at(
                    one_lvl,
                    int_ty,
                    one_lvl,
                    int_ty,
                    left,
                    right,
                    ih,
                    &|d2, z| plus_one(d2, z),
                )
            },
            k,
        );
        let conclusion = motive(dev, k);
        let statement = dev.pi_fv(k_fv, nat_ty, conclusion);
        let value = dev.lam_fv(k_fv, nat_ty, proof);
        dev.declare_theorem_u(names.iter_at_int, vec![], statement, value)?;
    }

    {
        let structure = Structure {
            level: one_lvl,
            nat_iter,
            iter: names.iter,
            carrier: int_ty,
            point: izero(dev),
            up: int_up,
            down: int_down,
        };
        let prelude = dev.int_prelude();
        let one = ione(dev);
        let zero = izero(dev);
        let minus = ineg(dev, one);

        // `(x + 1) + (−1) = x` and `(x + (−1)) + 1 = x`.
        let cancel = |d: &mut CharDev<'_>, first: ExprId, second: ExprId, zero_proof: ExprId| {
            let x_fv = d.fresh_fvar();
            let x = d.kernel().fvar(x_fv);
            let shifted = iadd(d, x, first);
            let restored = iadd(d, shifted, second);
            let inner_sum = iadd(d, first, second);
            let regrouped = iadd(d, x, inner_sum);
            let with_zero = iadd(d, x, zero);
            let int_ty = d.int_ty();
            let assoc = d.const_app(prelude.add_assoc, &[x, first, second]);
            let collapsed = d.congr_at(
                one_lvl,
                int_ty,
                one_lvl,
                int_ty,
                inner_sum,
                zero,
                zero_proof,
                &|d2, z| iadd(d2, x, z),
            );
            let absorbed = d.const_app(prelude.add_zero, &[x]);
            let prefix = d.trans_at(
                one_lvl, int_ty, restored, regrouped, with_zero, assoc, collapsed,
            );
            let body = d.trans_at(one_lvl, int_ty, restored, with_zero, x, prefix, absorbed);
            d.lam_fv(x_fv, int_ty, body)
        };
        let one_minus = iadd(dev, one, minus);
        let minus_one_sum = iadd(dev, minus, one);
        let add_neg_one = dev.const_app(prelude.add_neg, &[one]);
        let commuted = dev.const_app(prelude.add_comm, &[minus, one]);
        let flipped = dev.trans_at(
            one_lvl,
            int_ty,
            minus_one_sum,
            one_minus,
            zero,
            commuted,
            add_neg_one,
        );
        let left_proof = cancel(dev, one, minus, add_neg_one);
        let right_proof = cancel(dev, minus, one, flipped);
        let generation_proof = dev.kernel().const_(int.induction, vec![]);

        // Aperiodicity: `0 = up^(n+1) 0` would make `0 = ofNat (n+1)` and hence
        // `Nat.zero = Nat.succ n` after `Int.natAbs`.
        let aperiodic_proof = {
            let n_fv = dev.fresh_fvar();
            let n = dev.kernel().fvar(n_fv);
            let succ_n = dev.succ(n);
            let iterated = uiter(dev, structure, succ_n);
            let equation = dev.eq_at(one_lvl, int_ty, zero, iterated);
            let h_fv = dev.fresh_fvar();
            let h = dev.kernel().fvar(h_fv);
            let bridge = {
                let cst = dev.kernel().const_(names.iter_at_int, vec![]);
                dev.apply(cst, &[succ_n])
            };
            let value = of_nat(dev, succ_n);
            let chained = dev.trans_at(one_lvl, int_ty, zero, iterated, value, h, bridge);
            let magnitude = dev.congr_at(
                one_lvl,
                int_ty,
                one_lvl,
                nat_ty,
                zero,
                value,
                chained,
                &|d, z| {
                    let name = d.int_prelude().nat_abs;
                    d.const_app(name, &[z])
                },
            );
            let zero_ne_succ = dev.kernel().const_(nat.zero_ne_succ, vec![]);
            let contradiction = dev.apply(zero_ne_succ, &[n, magnitude]);
            let inner = dev.lam_fv(h_fv, equation, contradiction);
            dev.lam_fv(n_fv, nat_ty, inner)
        };

        let head = dev.kernel().const_(names.categorical, vec![one_lvl]);
        let applied = dev.apply(
            head,
            &[
                int_ty,
                zero,
                int_up,
                int_down,
                left_proof,
                right_proof,
                generation_proof,
                aperiodic_proof,
            ],
        );
        let statement = dev.kernel().infer(applied)?;
        dev.declare_theorem_u(names.categorical_at_int, vec![], statement, applied)?;
    }

    Ok(names)
}
