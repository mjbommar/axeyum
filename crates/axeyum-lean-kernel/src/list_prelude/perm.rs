//! `List.Perm` — a **decidable `Bool` predicate** deciding whether two
//! `List Nat`s agree on the multiplicity of every value, together with
//! `perm_refl`/`perm_symm`/`perm_reverse`/`perm_append_comm`.
//!
//! # The shape: `Nat.Finset.allBelow`, reused directly
//!
//! ADR-1577 declared `Nat.Finset.allBelow : (Nat → Bool) → Nat → Bool` — a
//! bounded `Bool`-valued universal, `allBelow f n := Nat.rec true (fun k ih
//! => if f k then ih else false) n` — together with its two reflection
//! theorems, `allBelow_of_all_true` (a pointwise fact below the bound makes
//! the loop `true`) and `allBelow_true_at` (the converse: a `true` loop
//! yields the pointwise fact below the bound). Both are plain functions, not
//! tied to `Nat.Finset`'s own carrier data, so this module reuses them
//! directly rather than rebuilding an equivalent loop:
//!
//! ```text
//! List.Perm l1 l2 := Nat.Finset.allBelow
//!   (fun a => Nat.beq (List.count a l1) (List.count a l2))
//!   (Nat.succ (Nat.add (List.max l1) (List.max l2)))
//! ```
//!
//! `List.max l := List.foldr Max.max Nat.zero l` — the largest element of
//! `l`, or `0` for `nil`. The bound only has to be *some* upper bound past
//! which both lists' counts are `0`; nothing below needs it proved tight, but
//! **it does need to be a genuine upper bound** for `Perm` to compute the
//! right `Bool` at concrete lists — see the module tests' negative controls
//! (`Perm [1,2] [1,2,2]` must reduce to `false`, which needs the bound to
//! reach index `2`).
//!
//! # What each theorem actually needs from the bound
//!
//! None of the four target theorems needs `List.max` proved to be an actual
//! upper bound, which was not obvious going in:
//!
//! - `perm_refl`/`perm_reverse`/`perm_append_comm` all reduce to a pointwise
//!   count identity that holds **unconditionally, for every `a`** (`beq_refl`,
//!   [`declare_count_reverse`], [`declare_count_append`] + `Nat.add_comm`
//!   respectively) — `allBelow_of_all_true`'s hypothesis is `∀ i, Lt i n → …`,
//!   and an unconditional pointwise proof discharges that for *any* `n`
//!   whatsoever, so the specific bound value never has to be reasoned about.
//! - `perm_symm` is the one exception: its hypothesis (`allBelow_true_at`)
//!   only gives the pointwise fact **below `bound(l1,l2)`**, and the goal
//!   needs it below `bound(l2,l1)`. Those are two different terms
//!   (`succ (add (max l1) (max l2))` vs. `succ (add (max l2) (max l1))`), so
//!   closing the gap needs `Nat.add_comm` + a `succ` congruence to prove
//!   `Eq (bound l1 l2) (bound l2 l1)` OUTRIGHT, then a congruence on
//!   `allBelow`'s own second argument to transport the `Bool` value across
//!   it. This is the only place any bound-symmetry reasoning is needed at
//!   all — none of the other three theorems' bounds are ever compared to
//!   another bound.
//!
//! # The two prerequisites `List` didn't have yet
//!
//! - [`declare_count_append`] — `List.count_append : ∀ a l1 l2, count a
//!   (append l1 l2) = add (count a l1) (count a l2)`. Same shape as
//!   `bridge::declare_length_append`'s induction on `l1`, but `count`'s cons
//!   case carries an extra `Bool.rec` on `Nat.beq head a` that `length`'s
//!   does not, so the step needs the SAME case split
//!   `bridge::declare_count_to_multiset` already built (`ops::
//!   bool_true_or_false_of`/`or_cases_of`) — unlike that proof, no
//!   `Nat.beq_comm` flip is needed here, because both sides of the goal
//!   split on the exact same `beq head a` term (no swapped-argument
//!   `Multiset.singleton` to reconcile).
//! - [`declare_count_reverse`] — `List.count_reverse : ∀ a l, count a l =
//!   count a (reverse l)`, by induction on `l`. The `nil` case is `Eq.refl`
//!   (`reverse nil ≡ nil`). The `cons` case unfolds `reverse (cons head
//!   tail)` to `append (reverse tail) (singleton head)` (exactly
//!   `theorems::declare_list_theorems`'s own `reverse` unfold), applies
//!   `count_append` to split that count into a sum, and closes with the same
//!   `beq head a` case split (needed again because `count a (cons head nil)`
//!   is itself `Bool.rec`-shaped) plus the induction hypothesis.

#![allow(
    clippy::many_single_char_names,
    clippy::wildcard_imports,
    clippy::too_many_lines,
    clippy::similar_names
)]

use super::ListNames;
use super::bridge::ListNatBridge;
use super::ops::*;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError, NatPrelude};

use super::ListPrelude;

/// The interned names [`build_list_perm`] adds on top of [`ListPrelude`],
/// [`NatPrelude`] and [`ListNatBridge`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ListPerm {
    /// `List.max : List Nat → Nat := List.foldr Max.max Nat.zero`.
    pub max: NameId,
    /// `List.count_append : ∀ a l1 l2, count a (append l1 l2) =
    /// add (count a l1) (count a l2)`.
    pub count_append: NameId,
    /// `List.count_reverse : ∀ a l, count a l = count a (reverse l)`.
    pub count_reverse: NameId,
    /// `List.Perm : List Nat → List Nat → Bool`.
    pub perm: NameId,
    /// `List.perm_refl : ∀ l, Eq Bool (Perm l l) true`.
    pub perm_refl: NameId,
    /// `List.perm_symm : ∀ l1 l2, Eq Bool (Perm l1 l2) true →
    /// Eq Bool (Perm l2 l1) true`.
    pub perm_symm: NameId,
    /// `List.perm_reverse : ∀ l, Eq Bool (Perm l (reverse l)) true`.
    pub perm_reverse: NameId,
    /// `List.perm_append_comm : ∀ l1 l2,
    /// Eq Bool (Perm (append l1 l2) (append l2 l1)) true`.
    pub perm_append_comm: NameId,
}

/// Build [`ListPerm`] on top of an already-built [`ListPrelude`]/
/// [`NatPrelude`]/[`ListNatBridge`] (from [`super::build_list_nat_bridge`]).
///
/// # Errors
///
/// Returns the trusted gate's rejection from any declaration here.
pub fn build_list_perm(
    kernel: &mut Kernel,
    list: &ListPrelude,
    nat: &NatPrelude,
    bridge: &ListNatBridge,
) -> Result<ListPerm, KernelError> {
    let logic = nat.logic;
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);

    let names = ListNames {
        list: list.list,
        nil: list.nil,
        cons: list.cons,
        rec: list.rec,
        u_param: list.u_param,
        length: list.length,
        append: list.append,
        map: list.map,
        foldr: list.foldr,
        reverse: list.reverse,
    };

    let count_append =
        declare_count_append(kernel, &logic, nat, &names, bridge.count, zero_lvl, one_lvl)?;
    let count_reverse = declare_count_reverse(
        kernel,
        &logic,
        nat,
        &names,
        bridge.count,
        count_append,
        zero_lvl,
        one_lvl,
    )?;

    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let foldr_const = kernel.const_(names.foldr, vec![]);
    let max_max_const = kernel.const_(nat.max_max, vec![]);
    let zero_const = kernel.const_(nat.zero, vec![]);

    // --- List.max : List Nat -> Nat := List.foldr Max.max Nat.zero -------
    let max = {
        let name = kernel.name_str(names.list, "max");
        let l_fv = 94_200;
        let l = kernel.fvar(l_fv);
        let body = apply_all(
            kernel,
            foldr_const,
            &[nat_const, nat_const, max_max_const, zero_const, l],
        );
        let value = lam_fvar(kernel, l_fv, list_nat, body, BinderInfo::Default);
        let ty = pi_fvar(kernel, l_fv, list_nat, nat_const, BinderInfo::Default);
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: crate::env::ReducibilityHint::Regular(3),
        })?;
        name
    };
    let max_const = kernel.const_(max, vec![]);

    // --- Perm : List Nat -> List Nat -> Bool ------------------------------
    // Perm l1 l2 := allBelow (fun a => beq (count a l1) (count a l2))
    //                        (succ (add (max l1) (max l2)))
    let perm = {
        let name = kernel.name_str(names.list, "Perm");
        let l1_fv = 94_201;
        let l2_fv = 94_202;
        let a_fv = 94_203;
        let l1 = kernel.fvar(l1_fv);
        let l2 = kernel.fvar(l2_fv);
        let count_const = kernel.const_(bridge.count, vec![]);
        let beq_const = kernel.const_(nat.beq, vec![]);
        let succ_const = kernel.const_(nat.succ, vec![]);
        let add_const = kernel.const_(nat.add, vec![]);
        let all_below_const = kernel.const_(nat.finset_all_below, vec![]);

        let predicate = {
            let a = kernel.fvar(a_fv);
            let c1 = apply_all(kernel, count_const, &[a, l1]);
            let c2 = apply_all(kernel, count_const, &[a, l2]);
            let body = apply_all(kernel, beq_const, &[c1, c2]);
            lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
        };
        let bound = {
            let m1 = kernel.app(max_const, l1);
            let m2 = kernel.app(max_const, l2);
            let s = apply_all(kernel, add_const, &[m1, m2]);
            kernel.app(succ_const, s)
        };
        let body = apply_all(kernel, all_below_const, &[predicate, bound]);
        let value = {
            let with_l2 = lam_fvar(kernel, l2_fv, list_nat, body, BinderInfo::Default);
            lam_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default)
        };
        let bool_ty = kernel.const_(logic.bool_, vec![]);
        let ty = {
            let with_l2 = pi_fvar(kernel, l2_fv, list_nat, bool_ty, BinderInfo::Default);
            pi_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default)
        };
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: crate::env::ReducibilityHint::Regular(4),
        })?;
        name
    };

    let perm_refl = declare_perm_refl(kernel, &logic, nat, &names, bridge, max, perm, zero_lvl)?;
    let perm_symm = declare_perm_symm(kernel, &logic, nat, &names, bridge, max, perm, zero_lvl)?;
    let perm_reverse = declare_perm_reverse(
        kernel,
        &logic,
        nat,
        &names,
        bridge,
        max,
        perm,
        count_reverse,
        zero_lvl,
    )?;
    let perm_append_comm = declare_perm_append_comm(
        kernel,
        &logic,
        nat,
        &names,
        bridge,
        max,
        perm,
        count_append,
        zero_lvl,
    )?;

    Ok(ListPerm {
        max,
        count_append,
        count_reverse,
        perm,
        perm_refl,
        perm_symm,
        perm_reverse,
        perm_append_comm,
    })
}

/// `List.count_append : ∀ a l1 l2, count a (append l1 l2) =
/// add (count a l1) (count a l2)`, by induction on `l1`.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_count_append(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    count: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "count_append");
    let a_fv = 94_000;
    let l1_fv = 94_001;
    let l2_fv = 94_002;
    let head_fv = 94_003;
    let tail_fv = 94_004;
    let ih_fv = 94_005;
    let x_fv = 94_006;
    let symm_base_fv = 94_010;
    let split_motive_fv = 94_020;
    let true_branch_fv = 94_021;
    let false_branch_fv = 94_022;
    let congr_l_true_fv = 94_030;
    let congr_m_true_fv = 94_031;
    let trans_true_fv1 = 94_032;
    let trans_true_fv2 = 94_033;
    let symm_true_fv = 94_034;
    let congr_l_false_fv = 94_040;
    let congr_m_false_fv = 94_041;
    let trans_false_fv1 = 94_042;
    let symm_false_fv = 94_043;

    let a = kernel.fvar(a_fv);
    let l2 = kernel.fvar(l2_fv);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let bool_true = kernel.const_(logic.bool_true, vec![]);
    let bool_false = kernel.const_(logic.bool_false, vec![]);
    let bool_rec_nat = kernel.const_(logic.bool_rec, vec![one_lvl]);

    let zero_const = kernel.const_(nat.zero, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let count_const = kernel.const_(count, vec![]);
    let append_const = kernel.const_(names.append, vec![]);

    let count_of = |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, count_const, &[a, x]) };
    let append_of = |k: &mut Kernel, x: ExprId, y: ExprId| -> ExprId {
        apply_all(k, append_const, &[nat_const, x, y])
    };

    let count_l2 = count_of(kernel, l2);

    let p = |k: &mut Kernel, x: ExprId| -> ExprId {
        let ax = append_of(k, x, l2);
        let lhs = count_of(k, ax);
        let cx = count_of(k, x);
        let rhs = apply_all(k, add_const, &[cx, count_l2]);
        eq_of(k, logic, one_lvl, nat_const, lhs, rhs)
    };

    // nil : Eq (count a (append nil l2)) (add (count a nil) (count a l2))
    // both sides defeq-reduced: LHS to `count a l2`, RHS to `add 0 (count a l2)`.
    let base = |k: &mut Kernel| -> ExprId {
        let zero_add_const = k.const_(nat.zero_add, vec![]);
        let h = k.app(zero_add_const, count_l2);
        let add0 = apply_all(k, add_const, &[zero_const, count_l2]);
        symm_of(
            k,
            logic,
            one_lvl,
            nat_const,
            add0,
            count_l2,
            h,
            symm_base_fv,
        )
    };

    let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
        // L' := count a (append (cons head tail) l2), reduced:
        //   Bool.rec (fun _ => Nat) (count a (append tail l2))
        //            (succ (count a (append tail l2))) (beq head a).
        let append_tail_l2 = append_of(k, tail, l2);
        let count_append_tail_l2 = count_of(k, append_tail_l2);
        let succ_count_append_tail_l2 = k.app(succ_const, count_append_tail_l2);
        let beq_head_a = apply_all(k, beq_const, &[head, a]);
        let motive_nat = {
            let anon = k.anon();
            k.lam(anon, bool_ty, nat_const, BinderInfo::Default)
        };
        let l_term = apply_all(
            k,
            bool_rec_nat,
            &[
                motive_nat,
                count_append_tail_l2,
                succ_count_append_tail_l2,
                beq_head_a,
            ],
        );

        // M' := count a (cons head tail), reduced the same way over `count a tail`.
        let count_tail = count_of(k, tail);
        let succ_count_tail = k.app(succ_const, count_tail);
        let m_term = apply_all(
            k,
            bool_rec_nat,
            &[motive_nat, count_tail, succ_count_tail, beq_head_a],
        );
        let r_term = apply_all(k, add_const, &[m_term, count_l2]);

        let r_tail = apply_all(k, add_const, &[count_tail, count_l2]);

        let split = bool_true_or_false_of(k, logic, one_lvl, beq_head_a, split_motive_fv);
        let left_ty = eq_of(k, logic, one_lvl, bool_ty, beq_head_a, bool_true);
        let right_ty = eq_of(k, logic, one_lvl, bool_ty, beq_head_a, bool_false);
        let goal = eq_of(k, logic, one_lvl, nat_const, l_term, r_term);

        let true_minor = {
            let ht = k.fvar(true_branch_fv);
            let hl_true = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_true,
                ht,
                congr_l_true_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[
                            motive_nat,
                            count_append_tail_l2,
                            succ_count_append_tail_l2,
                            x,
                        ],
                    )
                },
            );
            // hm_true : Eq m_term succ_count_tail
            let hm_true = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_true,
                ht,
                congr_m_true_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[motive_nat, count_tail, succ_count_tail, x],
                    )
                },
            );
            // hcongr_ih : Eq succ_count_append_tail_l2 (succ r_tail)
            let hcongr_ih = congr_of(
                k,
                logic,
                one_lvl,
                nat_const,
                one_lvl,
                nat_const,
                count_append_tail_l2,
                r_tail,
                ih,
                congr_m_true_fv + 1,
                &|k2, x| k2.app(succ_const, x),
            );
            // h_l_to_succ_rtail : Eq l_term (succ r_tail)
            let succ_r_tail = k.app(succ_const, r_tail);
            let h_l_to_succ_rtail = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                succ_count_append_tail_l2,
                succ_r_tail,
                hl_true,
                hcongr_ih,
                trans_true_fv1,
            );
            // succ_add(count_tail, count_l2) : Eq (add (succ count_tail) count_l2) (succ (add count_tail count_l2))
            let succ_add_const = k.const_(nat.succ_add, vec![]);
            let h_succ_add = apply_all(k, succ_add_const, &[count_tail, count_l2]);
            let add_succ_count_tail_l2 = apply_all(k, add_const, &[succ_count_tail, count_l2]);
            // h_succ_rtail_to_addsucc : Eq (succ r_tail) (add succ_count_tail count_l2)
            let h_succ_rtail_to_addsucc = symm_of(
                k,
                logic,
                one_lvl,
                nat_const,
                add_succ_count_tail_l2,
                succ_r_tail,
                h_succ_add,
                symm_true_fv,
            );
            // h_l_to_addsucc : Eq l_term (add succ_count_tail count_l2)
            let h_l_to_addsucc = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                succ_r_tail,
                add_succ_count_tail_l2,
                h_l_to_succ_rtail,
                h_succ_rtail_to_addsucc,
                trans_true_fv2,
            );
            // hr_true : Eq (add succ_count_tail count_l2) r_term  -- via congr(symm hm_true)
            // hm_true : Eq m_term succ_count_tail, so symm_of's (a,b) must
            // match hm_true's OWN direction (m_term, succ_count_tail), not
            // the desired output direction.
            let hm_true_symm = symm_of(
                k,
                logic,
                one_lvl,
                nat_const,
                m_term,
                succ_count_tail,
                hm_true,
                symm_true_fv + 1,
            );
            let hr_true = congr_of(
                k,
                logic,
                one_lvl,
                nat_const,
                one_lvl,
                nat_const,
                succ_count_tail,
                m_term,
                hm_true_symm,
                congr_m_true_fv + 2,
                &|k2, x| apply_all(k2, add_const, &[x, count_l2]),
            );
            let body = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                add_succ_count_tail_l2,
                r_term,
                h_l_to_addsucc,
                hr_true,
                trans_true_fv2 + 1,
            );
            lam_fvar(k, true_branch_fv, left_ty, body, BinderInfo::Default)
        };

        let false_minor = {
            let hf = k.fvar(false_branch_fv);
            let hl_false = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_false,
                hf,
                congr_l_false_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[
                            motive_nat,
                            count_append_tail_l2,
                            succ_count_append_tail_l2,
                            x,
                        ],
                    )
                },
            );
            // hm_false : Eq m_term count_tail
            let hm_false = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_false,
                hf,
                congr_m_false_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[motive_nat, count_tail, succ_count_tail, x],
                    )
                },
            );
            // L' -> count_append_tail_l2 -> r_tail [ih]
            let h_l_to_rtail = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                count_append_tail_l2,
                r_tail,
                hl_false,
                ih,
                trans_false_fv1,
            );
            // r_term -> add(count_tail,count_l2) = r_tail [congr symm hm_false]
            // hm_false : Eq m_term count_tail, so symm_of's (a,b) must match
            // that direction, not the desired output direction.
            let hm_false_symm = symm_of(
                k,
                logic,
                one_lvl,
                nat_const,
                m_term,
                count_tail,
                hm_false,
                symm_false_fv,
            );
            let h_rterm_to_rtail = congr_of(
                k,
                logic,
                one_lvl,
                nat_const,
                one_lvl,
                nat_const,
                count_tail,
                m_term,
                hm_false_symm,
                congr_m_false_fv + 1,
                &|k2, x| apply_all(k2, add_const, &[x, count_l2]),
            );
            // r_term = add(m_term,count_l2); h_rterm_to_rtail : Eq (add count_tail count_l2) (add m_term count_l2) = Eq r_tail r_term
            let h_rtail_to_rterm = h_rterm_to_rtail;
            let body = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                r_tail,
                r_term,
                h_l_to_rtail,
                h_rtail_to_rterm,
                trans_false_fv1 + 1,
            );
            lam_fvar(k, false_branch_fv, right_ty, body, BinderInfo::Default)
        };

        or_cases_of(
            k,
            logic,
            left_ty,
            right_ty,
            goal,
            true_minor,
            false_minor,
            split,
        )
    };

    let target = kernel.fvar(l1_fv);
    let proof = list_induct_prop(
        kernel, names, nat_const, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
    );
    let concl_ty = p(kernel, target);
    let value = {
        let with_l2 = lam_fvar(kernel, l2_fv, list_nat, proof, BinderInfo::Default);
        let with_l1 = lam_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default);
        lam_fvar(kernel, a_fv, nat_const, with_l1, BinderInfo::Default)
    };
    let ty = {
        let with_l2 = pi_fvar(kernel, l2_fv, list_nat, concl_ty, BinderInfo::Default);
        let with_l1 = pi_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default);
        pi_fvar(kernel, a_fv, nat_const, with_l1, BinderInfo::Default)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `List.count_reverse : ∀ a l, count a l = count a (reverse l)`, by
/// induction on `l`, using [`declare_count_append`].
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_count_reverse(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    count: NameId,
    count_append: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "count_reverse");
    let a_fv = 94_100;
    let l_fv = 94_101;
    let head_fv = 94_102;
    let tail_fv = 94_103;
    let ih_fv = 94_104;
    let x_fv = 94_105;
    let split_motive_fv = 94_110;
    let true_branch_fv = 94_111;
    let false_branch_fv = 94_112;
    let congr_l_true_fv = 94_120;
    let congr_s_true_fv = 94_121;
    let congr_l_false_fv = 94_122;
    let congr_s_false_fv = 94_123;
    let symm_true_fv = 94_130;
    let symm_false_fv = 94_131;
    let trans_true_fv = 94_140;
    let trans_false_fv = 94_141;
    let symm_r1r2_fv = 94_150;
    let symm_countapp_fv = 94_151;
    let trans_outer1_fv = 94_152;
    let trans_outer2_fv = 94_153;
    let congr_r1r2_fv = 94_154;
    let symm_ih_fv = 94_155;

    let a = kernel.fvar(a_fv);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let bool_true = kernel.const_(logic.bool_true, vec![]);
    let bool_false = kernel.const_(logic.bool_false, vec![]);
    let bool_rec_nat = kernel.const_(logic.bool_rec, vec![one_lvl]);

    let zero_const = kernel.const_(nat.zero, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let count_const = kernel.const_(count, vec![]);
    let append_const = kernel.const_(names.append, vec![]);
    let reverse_const = kernel.const_(names.reverse, vec![]);
    let cons_const = kernel.const_(names.cons, vec![zero_lvl]);
    let nil_const = kernel.const_(names.nil, vec![zero_lvl]);
    let count_append_const = kernel.const_(count_append, vec![]);

    let count_of = |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, count_const, &[a, x]) };
    let reverse_of =
        |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, reverse_const, &[nat_const, x]) };

    let p = |k: &mut Kernel, x: ExprId| -> ExprId {
        let lhs = count_of(k, x);
        let rx = reverse_of(k, x);
        let rhs = count_of(k, rx);
        eq_of(k, logic, one_lvl, nat_const, lhs, rhs)
    };

    // nil : reverse nil is defeq nil, so both sides are literally the same
    // term -- Eq.refl.
    let base = |k: &mut Kernel| -> ExprId {
        let nil_alpha = k.app(nil_const, nat_const);
        let count_nil = count_of(k, nil_alpha);
        refl_of(k, logic, one_lvl, nat_const, count_nil)
    };

    let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
        // L := count a (cons head tail), reduced.
        let count_tail = count_of(k, tail);
        let succ_count_tail = k.app(succ_const, count_tail);
        let beq_head_a = apply_all(k, beq_const, &[head, a]);
        let motive_nat = {
            let anon = k.anon();
            k.lam(anon, bool_ty, nat_const, BinderInfo::Default)
        };
        let l_term = apply_all(
            k,
            bool_rec_nat,
            &[motive_nat, count_tail, succ_count_tail, beq_head_a],
        );

        // singleton := cons head nil; S := count a singleton, reduced.
        let nil_alpha = k.app(nil_const, nat_const);
        let singleton = apply_all(k, cons_const, &[nat_const, head, nil_alpha]);
        let count_nil = count_of(k, nil_alpha);
        let succ_count_nil = k.app(succ_const, count_nil);
        let s_term = apply_all(
            k,
            bool_rec_nat,
            &[motive_nat, count_nil, succ_count_nil, beq_head_a],
        );

        // R2 := add count_tail s_term -- what the case split below shows
        // equals `L`.
        let r2 = apply_all(k, add_const, &[count_tail, s_term]);

        let split = bool_true_or_false_of(k, logic, one_lvl, beq_head_a, split_motive_fv);
        let left_ty = eq_of(k, logic, one_lvl, bool_ty, beq_head_a, bool_true);
        let right_ty = eq_of(k, logic, one_lvl, bool_ty, beq_head_a, bool_false);
        let goal = eq_of(k, logic, one_lvl, nat_const, l_term, r2);

        let true_minor = {
            let ht = k.fvar(true_branch_fv);
            let hl_true = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_true,
                ht,
                congr_l_true_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[motive_nat, count_tail, succ_count_tail, x],
                    )
                },
            );
            // hs_true : Eq s_term succ_count_nil, defeq succ zero
            let hs_true = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_true,
                ht,
                congr_s_true_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[motive_nat, count_nil, succ_count_nil, x],
                    )
                },
            );
            // congr on add: Eq (add count_tail s_term) (add count_tail succ_count_nil)
            // -- and `add count_tail succ_count_nil` is defeq `succ count_tail`
            // (`add X (succ Y) ~ succ (add X Y)`, `add X 0 ~ X`, both `refl`).
            let hcongr_add = congr_of(
                k,
                logic,
                one_lvl,
                nat_const,
                one_lvl,
                nat_const,
                s_term,
                succ_count_nil,
                hs_true,
                congr_s_true_fv + 1,
                &|k2, x| apply_all(k2, add_const, &[count_tail, x]),
            );
            let add_ct_succ_cn = apply_all(k, add_const, &[count_tail, succ_count_nil]);
            // hcongr_add : Eq r2 add_ct_succ_cn (congr_of's own (a,b) order),
            // so symm_of's (a,b) must match THAT direction.
            let h_r2_to_succct = symm_of(
                k,
                logic,
                one_lvl,
                nat_const,
                r2,
                add_ct_succ_cn,
                hcongr_add,
                symm_true_fv,
            );
            let body = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                succ_count_tail,
                r2,
                hl_true,
                h_r2_to_succct,
                trans_true_fv,
            );
            lam_fvar(k, true_branch_fv, left_ty, body, BinderInfo::Default)
        };

        let false_minor = {
            let hf = k.fvar(false_branch_fv);
            let hl_false = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_false,
                hf,
                congr_l_false_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[motive_nat, count_tail, succ_count_tail, x],
                    )
                },
            );
            // hs_false : Eq s_term count_nil, defeq zero
            let hs_false = congr_of(
                k,
                logic,
                one_lvl,
                bool_ty,
                one_lvl,
                nat_const,
                beq_head_a,
                bool_false,
                hf,
                congr_s_false_fv,
                &|k2, x| {
                    apply_all(
                        k2,
                        bool_rec_nat,
                        &[motive_nat, count_nil, succ_count_nil, x],
                    )
                },
            );
            let hcongr_add = congr_of(
                k,
                logic,
                one_lvl,
                nat_const,
                one_lvl,
                nat_const,
                s_term,
                count_nil,
                hs_false,
                congr_s_false_fv + 1,
                &|k2, x| apply_all(k2, add_const, &[count_tail, x]),
            );
            let add_ct_cn = apply_all(k, add_const, &[count_tail, count_nil]);
            // hcongr_add : Eq r2 add_ct_cn (congr_of's own (a,b) order), so
            // symm_of's (a,b) must match THAT direction.
            let h_r2_to_ct = symm_of(
                k,
                logic,
                one_lvl,
                nat_const,
                r2,
                add_ct_cn,
                hcongr_add,
                symm_false_fv,
            );
            let body = trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                count_tail,
                r2,
                hl_false,
                h_r2_to_ct,
                trans_false_fv,
            );
            lam_fvar(k, false_branch_fv, right_ty, body, BinderInfo::Default)
        };

        let l_eq_r2 = or_cases_of(
            k,
            logic,
            left_ty,
            right_ty,
            goal,
            true_minor,
            false_minor,
            split,
        );

        // Now combine with `count_append` and `ih` to reach the real goal:
        // count a (reverse (cons head tail)) = count a (append (reverse tail) singleton)  [defeq]
        //   = add (count a (reverse tail)) (count a singleton)      [count_append]     =: R1
        //   = add (count a tail) (count a singleton)                [congr, symm ih]   =: R2
        let reverse_tail = reverse_of(k, tail);
        let count_reverse_tail = count_of(k, reverse_tail);
        let r1 = apply_all(k, add_const, &[count_reverse_tail, s_term]);
        let append_reverse_tail_singleton =
            apply_all(k, append_const, &[nat_const, reverse_tail, singleton]);
        let rhs_full = apply_all(k, count_const, &[a, append_reverse_tail_singleton]);
        let h_count_append = apply_all(k, count_append_const, &[a, reverse_tail, singleton]);
        // h_count_append : Eq rhs_full r1

        // ih : Eq count_tail count_reverse_tail (from `p`'s own (lhs, rhs)
        // order), so symm_of's (a,b) must match that direction.
        let ih_symm = symm_of(
            k,
            logic,
            one_lvl,
            nat_const,
            count_tail,
            count_reverse_tail,
            ih,
            symm_ih_fv,
        );
        let h_r1_to_r2 = congr_of(
            k,
            logic,
            one_lvl,
            nat_const,
            one_lvl,
            nat_const,
            count_reverse_tail,
            count_tail,
            ih_symm,
            congr_r1r2_fv,
            &|k2, x| apply_all(k2, add_const, &[x, s_term]),
        );
        // h_r1_to_r2 : Eq r1 r2

        let h_l_to_r1 = {
            let h_r2_to_r1 = symm_of(
                k,
                logic,
                one_lvl,
                nat_const,
                r1,
                r2,
                h_r1_to_r2,
                symm_r1r2_fv,
            );
            trans_of(
                k,
                logic,
                one_lvl,
                nat_const,
                l_term,
                r2,
                r1,
                l_eq_r2,
                h_r2_to_r1,
                trans_outer1_fv,
            )
        };
        let h_rhsfull_to_r1_symm = symm_of(
            k,
            logic,
            one_lvl,
            nat_const,
            rhs_full,
            r1,
            h_count_append,
            symm_countapp_fv,
        );
        // h_rhsfull_to_r1_symm : Eq r1 rhs_full
        trans_of(
            k,
            logic,
            one_lvl,
            nat_const,
            l_term,
            r1,
            rhs_full,
            h_l_to_r1,
            h_rhsfull_to_r1_symm,
            trans_outer2_fv,
        )
    };

    let _ = zero_const;
    let target = kernel.fvar(l_fv);
    let proof = list_induct_prop(
        kernel, names, nat_const, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
    );
    let concl_ty = p(kernel, target);
    let value = {
        let with_l = lam_fvar(kernel, l_fv, list_nat, proof, BinderInfo::Default);
        lam_fvar(kernel, a_fv, nat_const, with_l, BinderInfo::Default)
    };
    let ty = {
        let with_l = pi_fvar(kernel, l_fv, list_nat, concl_ty, BinderInfo::Default);
        pi_fvar(kernel, a_fv, nat_const, with_l, BinderInfo::Default)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `List.perm_refl : ∀ l, Eq Bool (Perm l l) true` — via
/// `allBelow_of_all_true` and `Nat.beq_refl`, unconditionally in `a`.
#[allow(clippy::too_many_arguments)]
fn declare_perm_refl(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    bridge: &ListNatBridge,
    max: NameId,
    perm: NameId,
    zero_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "perm_refl");
    let l_fv = 94_250;
    let a_fv = 94_251;
    let hi_fv = 94_252;

    let one_lvl = kernel.level_succ(zero_lvl);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let bool_true = kernel.const_(logic.bool_true, vec![]);
    let l = kernel.fvar(l_fv);

    let count_const = kernel.const_(bridge.count, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let all_below_of_all_true_const = kernel.const_(nat.finset_all_below_of_all_true, vec![]);
    let beq_refl_const = kernel.const_(nat.beq_refl, vec![]);
    let max_const = kernel.const_(max, vec![]);

    let predicate = {
        let a = kernel.fvar(a_fv);
        let c1 = apply_all(kernel, count_const, &[a, l]);
        let c2 = apply_all(kernel, count_const, &[a, l]);
        let body = apply_all(kernel, beq_const, &[c1, c2]);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };
    let bound = {
        let m = kernel.app(max_const, l);
        let s = apply_all(kernel, add_const, &[m, m]);
        kernel.app(succ_const, s)
    };

    // Pointwise proof, unconditional in `a`: `∀ a (h : Lt a bound), Eq Bool
    // (predicate a) true`, via `beq_refl (count a l)`.
    let pointwise = {
        let a = kernel.fvar(a_fv);
        let lt_ty = {
            let lt_const = kernel.const_(nat.lt, vec![]);
            apply_all(kernel, lt_const, &[a, bound])
        };
        let count_a_l = apply_all(kernel, count_const, &[a, l]);
        let refl_proof = kernel.app(beq_refl_const, count_a_l);
        let body = lam_fvar(kernel, hi_fv, lt_ty, refl_proof, BinderInfo::Default);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };

    let proof = apply_all(
        kernel,
        all_below_of_all_true_const,
        &[predicate, bound, pointwise],
    );
    let perm_const = kernel.const_(perm, vec![]);
    let perm_l_l = apply_all(kernel, perm_const, &[l, l]);
    let concl_ty = eq_of(kernel, logic, one_lvl, bool_ty, perm_l_l, bool_true);

    let value = lam_fvar(kernel, l_fv, list_nat, proof, BinderInfo::Default);
    let ty = pi_fvar(kernel, l_fv, list_nat, concl_ty, BinderInfo::Default);
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `List.perm_symm : ∀ l1 l2, Perm l1 l2 = true → Perm l2 l1 = true`.
///
/// The only one of the four that needs to relate `bound l1 l2` to
/// `bound l2 l1` — see the module doc.
#[allow(clippy::too_many_arguments, clippy::too_many_lines)]
fn declare_perm_symm(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    bridge: &ListNatBridge,
    max: NameId,
    perm: NameId,
    zero_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "perm_symm");
    let l1_fv = 94_260;
    let l2_fv = 94_261;
    let hp_fv = 94_262;
    let a_fv = 94_263;
    let hi_fv = 94_264;
    let symm_bound_fv = 94_270;
    let congr_bound_fv = 94_271;
    let symm_beq_fv = 94_272;
    let trans_beq_fv = 94_273;
    let congr_perm_fv = 94_274;

    let one_lvl = kernel.level_succ(zero_lvl);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let bool_true = kernel.const_(logic.bool_true, vec![]);
    let l1 = kernel.fvar(l1_fv);
    let l2 = kernel.fvar(l2_fv);

    let count_const = kernel.const_(bridge.count, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let all_below_of_all_true_const = kernel.const_(nat.finset_all_below_of_all_true, vec![]);
    let all_below_true_at_const = kernel.const_(nat.finset_all_below_true_at, vec![]);
    let beq_comm_const = kernel.const_(nat.beq_comm, vec![]);
    let add_comm_const = kernel.const_(nat.add_comm, vec![]);
    let max_const = kernel.const_(max, vec![]);
    let perm_const = kernel.const_(perm, vec![]);
    let lt_const = kernel.const_(nat.lt, vec![]);

    let max_l1 = kernel.app(max_const, l1);
    let max_l2 = kernel.app(max_const, l2);
    let bound12 = {
        let s = apply_all(kernel, add_const, &[max_l1, max_l2]);
        kernel.app(succ_const, s)
    };
    let bound21 = {
        let s = apply_all(kernel, add_const, &[max_l2, max_l1]);
        kernel.app(succ_const, s)
    };

    // Eq bound12 bound21, via Nat.add_comm + a `succ` congruence.
    let h_add_comm = apply_all(kernel, add_comm_const, &[max_l1, max_l2]);
    // h_add_comm : Eq (add max_l1 max_l2) (add max_l2 max_l1)
    let add_max_l1_l2 = apply_all(kernel, add_const, &[max_l1, max_l2]);
    let add_max_l2_l1 = apply_all(kernel, add_const, &[max_l2, max_l1]);
    let h_bound12_eq_bound21 = congr_of(
        kernel,
        logic,
        one_lvl,
        nat_const,
        one_lvl,
        nat_const,
        add_max_l1_l2,
        add_max_l2_l1,
        h_add_comm,
        congr_bound_fv,
        &|k2, x| k2.app(succ_const, x),
    );

    let predicate12 = {
        let a = kernel.fvar(a_fv);
        let c1 = apply_all(kernel, count_const, &[a, l1]);
        let c2 = apply_all(kernel, count_const, &[a, l2]);
        let body = apply_all(kernel, beq_const, &[c1, c2]);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };
    let predicate21 = {
        let a = kernel.fvar(a_fv);
        let c1 = apply_all(kernel, count_const, &[a, l2]);
        let c2 = apply_all(kernel, count_const, &[a, l1]);
        let body = apply_all(kernel, beq_const, &[c1, c2]);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };

    let perm_l1_l2 = apply_all(kernel, perm_const, &[l1, l2]);
    let hp = kernel.fvar(hp_fv);
    let hp_ty = eq_of(kernel, logic, one_lvl, bool_ty, perm_l1_l2, bool_true);

    // hp says: allBelow predicate12 bound12 = true (defeq unfold of `Perm`).
    // allBelow_true_at gives the pointwise fact below bound12.
    let hpt = apply_all(kernel, all_below_true_at_const, &[predicate12, bound12, hp]);

    // Build the pointwise proof needed for `allBelow_of_all_true` at
    // `predicate21`/`bound21`: `∀ a (h : Lt a bound21), Eq Bool (predicate21 a) true`.
    let pointwise21 = {
        let a = kernel.fvar(a_fv);
        let hi_ty = apply_all(kernel, lt_const, &[a, bound21]);
        let hi = kernel.fvar(hi_fv);
        // transport `hi : Lt a bound21` to `Lt a bound12` along
        // `Eq bound21 bound12` (symm of the add_comm-derived equality).
        let h_bound21_eq_bound12 = symm_of(
            kernel,
            logic,
            one_lvl,
            nat_const,
            bound12,
            bound21,
            h_bound12_eq_bound21,
            symm_bound_fv,
        );
        let hi_bound12 = transport_along(
            kernel,
            logic,
            one_lvl,
            nat_const,
            bound21,
            bound12,
            h_bound21_eq_bound12,
            congr_bound_fv + 1,
            hi,
            &|k2, x| apply_all(k2, lt_const, &[a, x]),
        );
        let h12 = apply_all(kernel, hpt, &[a, hi_bound12]);
        // h12 : Eq Bool (predicate12 a) true, i.e. beq (count a l1)(count a l2) = true.
        // Flip via beq_comm to get predicate21 a = beq (count a l2)(count a l1) = true.
        let c1 = apply_all(kernel, count_const, &[a, l1]);
        let c2 = apply_all(kernel, count_const, &[a, l2]);
        let h_comm = apply_all(kernel, beq_comm_const, &[c2, c1]);
        // h_comm : Eq (beq c2 c1) (beq c1 c2)
        let beq_c1_c2 = apply_all(kernel, beq_const, &[c1, c2]);
        let beq_c2_c1 = apply_all(kernel, beq_const, &[c2, c1]);
        let bool_true_lit = kernel.const_(logic.bool_true, vec![]);
        let h21 = trans_of(
            kernel,
            logic,
            one_lvl,
            bool_ty,
            beq_c2_c1,
            beq_c1_c2,
            bool_true_lit,
            h_comm,
            h12,
            trans_beq_fv,
        );
        let with_hi = lam_fvar(kernel, hi_fv, hi_ty, h21, BinderInfo::Default);
        lam_fvar(kernel, a_fv, nat_const, with_hi, BinderInfo::Default)
    };

    let proof21_at_bound21 = apply_all(
        kernel,
        all_below_of_all_true_const,
        &[predicate21, bound21, pointwise21],
    );
    let perm_l2_l1 = apply_all(kernel, perm_const, &[l2, l1]);
    let concl_ty = eq_of(kernel, logic, one_lvl, bool_ty, perm_l2_l1, bool_true);
    let _ = (symm_beq_fv, congr_perm_fv);

    let value = {
        let with_hp = lam_fvar(
            kernel,
            hp_fv,
            hp_ty,
            proof21_at_bound21,
            BinderInfo::Default,
        );
        let with_l2 = lam_fvar(kernel, l2_fv, list_nat, with_hp, BinderInfo::Default);
        lam_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default)
    };
    let ty = {
        let with_hp = pi_fvar(kernel, hp_fv, hp_ty, concl_ty, BinderInfo::Default);
        let with_l2 = pi_fvar(kernel, l2_fv, list_nat, with_hp, BinderInfo::Default);
        pi_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `List.perm_reverse : ∀ l, Eq Bool (Perm l (reverse l)) true` — via
/// [`declare_count_reverse`], unconditionally in `a`.
#[allow(clippy::too_many_arguments)]
fn declare_perm_reverse(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    bridge: &ListNatBridge,
    max: NameId,
    perm: NameId,
    count_reverse: NameId,
    zero_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "perm_reverse");
    let l_fv = 94_300;
    let a_fv = 94_301;
    let hi_fv = 94_302;

    let one_lvl = kernel.level_succ(zero_lvl);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let bool_true = kernel.const_(logic.bool_true, vec![]);
    let l = kernel.fvar(l_fv);

    let count_const = kernel.const_(bridge.count, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let all_below_of_all_true_const = kernel.const_(nat.finset_all_below_of_all_true, vec![]);
    let beq_eq_true_of_eq_const = kernel.const_(nat.beq_eq_true_of_eq, vec![]);
    let count_reverse_const = kernel.const_(count_reverse, vec![]);
    let reverse_const = kernel.const_(names.reverse, vec![]);
    let max_const = kernel.const_(max, vec![]);
    let lt_const = kernel.const_(nat.lt, vec![]);

    let reverse_l = apply_all(kernel, reverse_const, &[nat_const, l]);

    let predicate = {
        let a = kernel.fvar(a_fv);
        let c1 = apply_all(kernel, count_const, &[a, l]);
        let c2 = apply_all(kernel, count_const, &[a, reverse_l]);
        let body = apply_all(kernel, beq_const, &[c1, c2]);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };
    let bound = {
        let m1 = kernel.app(max_const, l);
        let m2 = kernel.app(max_const, reverse_l);
        let s = apply_all(kernel, add_const, &[m1, m2]);
        kernel.app(succ_const, s)
    };

    let pointwise = {
        let a = kernel.fvar(a_fv);
        let lt_ty = apply_all(kernel, lt_const, &[a, bound]);
        let count_reverse_applied = apply_all(kernel, count_reverse_const, &[a, l]);
        // count_reverse_applied : Eq Nat (count a l) (count a (reverse l))
        let count_a_l = apply_all(kernel, count_const, &[a, l]);
        let count_a_revl = apply_all(kernel, count_const, &[a, reverse_l]);
        let beq_true = apply_all(
            kernel,
            beq_eq_true_of_eq_const,
            &[count_a_l, count_a_revl, count_reverse_applied],
        );
        let body = lam_fvar(kernel, hi_fv, lt_ty, beq_true, BinderInfo::Default);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };

    let proof = apply_all(
        kernel,
        all_below_of_all_true_const,
        &[predicate, bound, pointwise],
    );
    let perm_const = kernel.const_(perm, vec![]);
    let perm_l_revl = apply_all(kernel, perm_const, &[l, reverse_l]);
    let concl_ty = eq_of(kernel, logic, one_lvl, bool_ty, perm_l_revl, bool_true);

    let value = lam_fvar(kernel, l_fv, list_nat, proof, BinderInfo::Default);
    let ty = pi_fvar(kernel, l_fv, list_nat, concl_ty, BinderInfo::Default);
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `List.perm_append_comm : ∀ l1 l2, Eq Bool (Perm (append l1 l2)
/// (append l2 l1)) true` — via [`declare_count_append`] (twice) and
/// `Nat.add_comm`, unconditionally in `a`.
#[allow(clippy::too_many_arguments)]
fn declare_perm_append_comm(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    bridge: &ListNatBridge,
    max: NameId,
    perm: NameId,
    count_append: NameId,
    zero_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "perm_append_comm");
    let l1_fv = 94_330;
    let l2_fv = 94_331;
    let a_fv = 94_332;
    let hi_fv = 94_333;
    let trans1_fv = 94_340;
    let trans2_fv = 94_341;
    let symm_fv = 94_342;

    let one_lvl = kernel.level_succ(zero_lvl);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let bool_ty = kernel.const_(logic.bool_, vec![]);
    let bool_true = kernel.const_(logic.bool_true, vec![]);
    let l1 = kernel.fvar(l1_fv);
    let l2 = kernel.fvar(l2_fv);

    let count_const = kernel.const_(bridge.count, vec![]);
    let beq_const = kernel.const_(nat.beq, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let all_below_of_all_true_const = kernel.const_(nat.finset_all_below_of_all_true, vec![]);
    let beq_eq_true_of_eq_const = kernel.const_(nat.beq_eq_true_of_eq, vec![]);
    let add_comm_const = kernel.const_(nat.add_comm, vec![]);
    let count_append_const = kernel.const_(count_append, vec![]);
    let append_const = kernel.const_(names.append, vec![]);
    let max_const = kernel.const_(max, vec![]);
    let lt_const = kernel.const_(nat.lt, vec![]);

    let append_l1_l2 = apply_all(kernel, append_const, &[nat_const, l1, l2]);
    let append_l2_l1 = apply_all(kernel, append_const, &[nat_const, l2, l1]);

    let predicate = {
        let a = kernel.fvar(a_fv);
        let c1 = apply_all(kernel, count_const, &[a, append_l1_l2]);
        let c2 = apply_all(kernel, count_const, &[a, append_l2_l1]);
        let body = apply_all(kernel, beq_const, &[c1, c2]);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };
    let bound = {
        let m1 = kernel.app(max_const, append_l1_l2);
        let m2 = kernel.app(max_const, append_l2_l1);
        let s = apply_all(kernel, add_const, &[m1, m2]);
        kernel.app(succ_const, s)
    };

    let pointwise = {
        let a = kernel.fvar(a_fv);
        let lt_ty = apply_all(kernel, lt_const, &[a, bound]);

        let count_a_l1 = apply_all(kernel, count_const, &[a, l1]);
        let count_a_l2 = apply_all(kernel, count_const, &[a, l2]);
        let count_a_append12 = apply_all(kernel, count_const, &[a, append_l1_l2]);
        let count_a_append21 = apply_all(kernel, count_const, &[a, append_l2_l1]);

        let h_ca1 = apply_all(kernel, count_append_const, &[a, l1, l2]);
        // h_ca1 : Eq count_a_append12 (add count_a_l1 count_a_l2)
        let h_ca2 = apply_all(kernel, count_append_const, &[a, l2, l1]);
        // h_ca2 : Eq count_a_append21 (add count_a_l2 count_a_l1)
        let h_comm = apply_all(kernel, add_comm_const, &[count_a_l1, count_a_l2]);
        // h_comm : Eq (add count_a_l1 count_a_l2) (add count_a_l2 count_a_l1)

        let add12 = apply_all(kernel, add_const, &[count_a_l1, count_a_l2]);
        let add21 = apply_all(kernel, add_const, &[count_a_l2, count_a_l1]);

        let h_step1 = trans_of(
            kernel,
            logic,
            one_lvl,
            nat_const,
            count_a_append12,
            add12,
            add21,
            h_ca1,
            h_comm,
            trans1_fv,
        );
        // h_step1 : Eq count_a_append12 add21
        // h_ca2 : Eq count_a_append21 add21, so symm_of's (a,b) must match
        // that direction.
        let h_ca2_symm = symm_of(
            kernel,
            logic,
            one_lvl,
            nat_const,
            count_a_append21,
            add21,
            h_ca2,
            symm_fv,
        );
        let h_full = trans_of(
            kernel,
            logic,
            one_lvl,
            nat_const,
            count_a_append12,
            add21,
            count_a_append21,
            h_step1,
            h_ca2_symm,
            trans2_fv,
        );
        // h_full : Eq count_a_append12 count_a_append21
        let beq_true = apply_all(
            kernel,
            beq_eq_true_of_eq_const,
            &[count_a_append12, count_a_append21, h_full],
        );
        let body = lam_fvar(kernel, hi_fv, lt_ty, beq_true, BinderInfo::Default);
        lam_fvar(kernel, a_fv, nat_const, body, BinderInfo::Default)
    };

    let proof = apply_all(
        kernel,
        all_below_of_all_true_const,
        &[predicate, bound, pointwise],
    );
    let perm_const = kernel.const_(perm, vec![]);
    let perm_lhs = apply_all(kernel, perm_const, &[append_l1_l2, append_l2_l1]);
    let concl_ty = eq_of(kernel, logic, one_lvl, bool_ty, perm_lhs, bool_true);

    let value = {
        let with_l2 = lam_fvar(kernel, l2_fv, list_nat, proof, BinderInfo::Default);
        lam_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default)
    };
    let ty = {
        let with_l2 = pi_fvar(kernel, l2_fv, list_nat, concl_ty, BinderInfo::Default);
        pi_fvar(kernel, l1_fv, list_nat, with_l2, BinderInfo::Default)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

#[cfg(test)]
mod perm_tests;
