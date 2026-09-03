//! The bridge between `List` and the rest of this prelude: `List.sum`
//! (needs `Nat.add`) and its theorems, plus `List.toMultiset`/`List.count`
//! and the theorem tying them to `Nat.Multiset.count` (ADR-1520) — so the
//! function-plus-bound `Nat.Multiset` carrier and the new ordinary
//! inductive `List` agree on how many times a value occurs.
//!
//! Everything here needs [`crate::build_nat_prelude`] (for `Nat.add` and its
//! theorems, and for `Nat.Multiset`), which is why it is a separate function
//! from [`super::build_list_prelude`] rather than folded into it: `List`
//! itself sits BEFORE `nat` in the prelude chain (`List Nat` only needs the
//! `Nat` type), but `List.sum`'s theorems need the real named `Nat.add` —
//! our own `Nat.add` recurses on its RIGHT argument, so `0 + x` and
//! `succ a + x` do not reduce for a symbolic `x` by defeq alone, and
//! reinventing `zero_add`/`succ_add`/`add_assoc` inline here would just
//! duplicate what `nat_prelude` already proves.

#![allow(
    clippy::many_single_char_names,
    clippy::wildcard_imports,
    clippy::too_many_lines
)]

use super::ListNames;
use super::ops::*;
use crate::env::{Declaration, ReducibilityHint};
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::name::NameId;
use crate::{BinderInfo, Kernel, KernelError, NatPrelude, build_nat_prelude};

use super::ListPrelude;

/// The interned names [`build_list_nat_bridge`] adds on top of
/// [`ListPrelude`] and [`NatPrelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ListNatBridge {
    /// `List.sum : List Nat → Nat := List.foldr Nat.add Nat.zero`.
    pub sum: NameId,
    /// `List.length_append : ∀ {α} l1 l2, length (append l1 l2) = length l1 + length l2`.
    pub length_append: NameId,
    /// `List.length_reverse : ∀ {α} l, length (reverse l) = length l`.
    pub length_reverse: NameId,
    /// `List.sum_append : ∀ l1 l2, sum (append l1 l2) = sum l1 + sum l2`.
    pub sum_append: NameId,
    /// `List.toMultiset : List Nat → Nat.Multiset`, folding `Multiset.add`/
    /// `singleton` over the list.
    pub to_multiset: NameId,
    /// `List.count : Nat → List Nat → Nat`, counting occurrences of `a` by
    /// `Nat.beq`.
    pub count: NameId,
    /// `List.count_toMultiset : ∀ a l, count a l = Nat.Multiset.count (toMultiset l) a`
    /// — landed only if it typechecks; see the module doc.
    pub count_to_multiset: Option<NameId>,
}

/// Build [`ListPrelude`], [`NatPrelude`], and the bridge between them.
///
/// # Errors
///
/// Returns the trusted gate's rejection from either prelude or from any
/// bridge declaration.
pub fn build_list_nat_bridge(
    kernel: &mut Kernel,
) -> Result<(ListPrelude, NatPrelude, ListNatBridge), KernelError> {
    let list = super::build_list_prelude(kernel)?;
    let nat = build_nat_prelude(kernel)?;
    let logic = nat.logic;
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    let type0 = kernel.sort(one_lvl);

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

    let nat_const = kernel.const_(nat.nat, vec![]);
    let foldr_const = kernel.const_(names.foldr, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let zero_const = kernel.const_(nat.zero, vec![]);

    // --- sum : List Nat -> Nat := foldr Nat Nat Nat.add Nat.zero ---------
    let sum = {
        let name = kernel.name_str(names.list, "sum");
        let l_fv = 92_000;
        let l = kernel.fvar(l_fv);
        let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
        let body = apply_all(
            kernel,
            foldr_const,
            &[nat_const, nat_const, add_const, zero_const, l],
        );
        let value = lam_fvar(kernel, l_fv, list_nat, body, BinderInfo::Default);
        let ty = pi_fvar(kernel, l_fv, list_nat, nat_const, BinderInfo::Default);
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
        name
    };
    let sum_const = kernel.const_(sum, vec![]);

    // --- length_append : forall {a} l1 l2, length (append l1 l2) = length l1 + length l2
    let length_append =
        declare_length_append(kernel, &logic, &nat, &names, zero_lvl, one_lvl, type0)?;

    // --- length_reverse : forall {a} l, length (reverse l) = length l ----
    let length_reverse = declare_length_reverse(
        kernel,
        &logic,
        &nat,
        &names,
        length_append,
        zero_lvl,
        one_lvl,
        type0,
    )?;

    // --- foldr_add_eq_sum_add : forall l z, foldr add z l = sum l + z ----
    let foldr_add_eq_sum_add =
        declare_foldr_add_eq_sum_add(kernel, &logic, &nat, &names, sum, zero_lvl, one_lvl)?;

    // --- sum_append : sum (append l1 l2) = sum l1 + sum l2 ---------------
    let sum_append = declare_sum_append(
        kernel,
        &logic,
        &nat,
        &names,
        sum,
        list.foldr_append,
        foldr_add_eq_sum_add,
        zero_lvl,
        one_lvl,
    )?;

    // --- toMultiset : List Nat -> Nat.Multiset ----------------------------
    let to_multiset = {
        let name = kernel.name_str(names.list, "toMultiset");
        let l_fv = 92_100;
        let head_fv = 92_101;
        let ih_fv = 92_102;
        let l = kernel.fvar(l_fv);
        let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
        let multiset_const = kernel.const_(nat.multiset, vec![]);
        let multiset_zero = kernel.const_(nat.multiset_zero, vec![]);
        let multiset_singleton = kernel.const_(nat.multiset_singleton, vec![]);
        let multiset_add = kernel.const_(nat.multiset_add, vec![]);

        // f := fun head ih => Multiset.add (Multiset.singleton head) ih
        let f = {
            let head = kernel.fvar(head_fv);
            let singleton_head = kernel.app(multiset_singleton, head);
            let ih = kernel.fvar(ih_fv);
            let added = apply_all(kernel, multiset_add, &[singleton_head, ih]);
            let inner = lam_fvar(kernel, ih_fv, multiset_const, added, BinderInfo::Default);
            lam_fvar(kernel, head_fv, nat_const, inner, BinderInfo::Default)
        };
        let body = apply_all(
            kernel,
            foldr_const,
            &[nat_const, multiset_const, f, multiset_zero, l],
        );
        let value = lam_fvar(kernel, l_fv, list_nat, body, BinderInfo::Default);
        let ty = pi_fvar(kernel, l_fv, list_nat, multiset_const, BinderInfo::Default);
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
        name
    };

    // --- count : Nat -> List Nat -> Nat, counting occurrences of `a` -----
    let count = {
        let name = kernel.name_str(names.list, "count");
        let a_fv = 92_200;
        let l_fv = 92_201;
        let head_fv = 92_202;
        let ih_fv = 92_203;
        let a = kernel.fvar(a_fv);
        let l = kernel.fvar(l_fv);
        let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
        let beq_const = kernel.const_(nat.beq, vec![]);
        let bool_rec = kernel.const_(logic.bool_rec, vec![one_lvl]);
        let succ_const = kernel.const_(nat.succ, vec![]);

        // f := fun head ih => Bool.rec (fun _ => Nat) ih (Nat.succ ih) (Nat.beq head a)
        let f = {
            let head = kernel.fvar(head_fv);
            let ih = kernel.fvar(ih_fv);
            let beq_head_a = apply_all(kernel, beq_const, &[head, a]);
            let succ_ih = kernel.app(succ_const, ih);
            let motive = {
                let dummy_fv = 92_204;
                let bool_ty = kernel.const_(logic.bool_, vec![]);
                lam_fvar(kernel, dummy_fv, bool_ty, nat_const, BinderInfo::Default)
            };
            let selected = apply_all(kernel, bool_rec, &[motive, ih, succ_ih, beq_head_a]);
            let inner = lam_fvar(kernel, ih_fv, nat_const, selected, BinderInfo::Default);
            lam_fvar(kernel, head_fv, nat_const, inner, BinderInfo::Default)
        };
        let body = apply_all(
            kernel,
            foldr_const,
            &[nat_const, nat_const, f, zero_const, l],
        );
        let value = {
            let with_l = lam_fvar(kernel, l_fv, list_nat, body, BinderInfo::Default);
            lam_fvar(kernel, a_fv, nat_const, with_l, BinderInfo::Default)
        };
        let ty = {
            let with_l = pi_fvar(kernel, l_fv, list_nat, nat_const, BinderInfo::Default);
            pi_fvar(kernel, a_fv, nat_const, with_l, BinderInfo::Default)
        };
        kernel.add_declaration(Declaration::Definition {
            name,
            uparams: vec![],
            ty,
            value,
            hint: ReducibilityHint::Regular(3),
        })?;
        name
    };

    let count_to_multiset =
        declare_count_to_multiset(kernel, &logic, &nat, &names, count, to_multiset, zero_lvl).ok();

    let _ = sum_const;

    Ok((
        list,
        nat,
        ListNatBridge {
            sum,
            length_append,
            length_reverse,
            sum_append,
            to_multiset,
            count,
            count_to_multiset,
        },
    ))
}

/// `∀ {α} l1 l2, length (append l1 l2) = length l1 + length l2`, by
/// induction on `l1`. Nil case needs `Nat.zero_add` (our `Nat.add` recurses
/// on its RIGHT argument, so `0 + length l2` does not reduce by defeq for a
/// symbolic `length l2`); cons case needs `Nat.succ_add`.
#[allow(clippy::too_many_arguments)]
fn declare_length_append(
    kernel: &mut Kernel,
    logic: &crate::LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "length_append");
    let alpha_fv = 92_300;
    let l1_fv = 92_301;
    let l2_fv = 92_302;
    let head_fv = 92_303;
    let tail_fv = 92_304;
    let ih_fv = 92_305;
    let x_fv = 92_306;
    let symm_x_fv = 92_307;
    let congr_x_fv = 92_308;
    let trans_x_fv = 92_309;

    let alpha = kernel.fvar(alpha_fv);
    let l2 = kernel.fvar(l2_fv);
    let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let append_const = kernel.const_(names.append, vec![]);
    let length_const = kernel.const_(names.length, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let succ_const = kernel.const_(nat.succ, vec![]);
    let zero_add_const = kernel.const_(nat.zero_add, vec![]);
    let succ_add_const = kernel.const_(nat.succ_add, vec![]);

    let length_of =
        |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, length_const, &[alpha, x]) };
    let length_l2 = length_of(kernel, l2);

    let p = |k: &mut Kernel, x: ExprId| -> ExprId {
        let append_x_l2 = apply_all(k, append_const, &[alpha, x, l2]);
        let lhs = apply_all(k, length_const, &[alpha, append_x_l2]);
        let length_x = apply_all(k, length_const, &[alpha, x]);
        let rhs = apply_all(k, add_const, &[length_x, length_l2]);
        eq_of(k, logic, one_lvl, nat_const, lhs, rhs)
    };
    let base = |k: &mut Kernel| -> ExprId {
        let zero_expr = k.const_(nat.zero, vec![]);
        let add0 = apply_all(k, add_const, &[zero_expr, length_l2]);
        let step = apply_all(k, zero_add_const, &[length_l2]);
        symm_of(
            k, logic, one_lvl, nat_const, add0, length_l2, step, symm_x_fv,
        )
    };
    // ih : length (append tail l2) = length tail + length l2
    // need: length (append (cons head tail) l2) = length (cons head tail) + length l2
    //   a := succ (length (append tail l2))     [LHS, defeq]
    //   b := succ (length tail + length l2)     [congr succ via ih: Eq a b]
    //   c := succ (length tail) + length l2     [RHS, defeq; succ_add: Eq c b]
    let step = |k: &mut Kernel, _head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
        let append_tail_l2 = apply_all(k, append_const, &[alpha, tail, l2]);
        let length_append_tail_l2 = apply_all(k, length_const, &[alpha, append_tail_l2]);
        let a = k.app(succ_const, length_append_tail_l2);

        let length_tail = apply_all(k, length_const, &[alpha, tail]);
        let add_lt_l2 = apply_all(k, add_const, &[length_tail, length_l2]);
        let b = k.app(succ_const, add_lt_l2);

        let h_congr = congr_of(
            k,
            logic,
            one_lvl,
            nat_const,
            one_lvl,
            nat_const,
            length_append_tail_l2,
            add_lt_l2,
            ih,
            congr_x_fv,
            &|k2, x| k2.app(succ_const, x),
        );

        let succ_length_tail = k.app(succ_const, length_tail);
        let c = apply_all(k, add_const, &[succ_length_tail, length_l2]);
        let succ_add_instance = apply_all(k, succ_add_const, &[length_tail, length_l2]);
        let b_eq_c = symm_of(
            k,
            logic,
            one_lvl,
            nat_const,
            c,
            b,
            succ_add_instance,
            symm_x_fv,
        );

        trans_of(
            k, logic, one_lvl, nat_const, a, b, c, h_congr, b_eq_c, trans_x_fv,
        )
    };
    let target = kernel.fvar(l1_fv);
    let proof = list_induct_prop(
        kernel, names, alpha, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
    );
    let concl_ty = p(kernel, target);
    let value = {
        let with_l2 = lam_fvar(kernel, l2_fv, list_alpha, proof, BinderInfo::Default);
        let with_l1 = lam_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
        lam_fvar(kernel, alpha_fv, type0, with_l1, BinderInfo::Implicit)
    };
    let ty = {
        let with_l2 = pi_fvar(kernel, l2_fv, list_alpha, concl_ty, BinderInfo::Default);
        let with_l1 = pi_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
        pi_fvar(kernel, alpha_fv, type0, with_l1, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `∀ {α} l, length (reverse l) = length l`, using `length_append`.
#[allow(clippy::too_many_arguments)]
fn declare_length_reverse(
    kernel: &mut Kernel,
    logic: &crate::LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    length_append: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "length_reverse");
    let alpha_fv = 92_400;
    let l_fv = 92_401;
    let head_fv = 92_402;
    let tail_fv = 92_403;
    let ih_fv = 92_404;
    let x_fv = 92_405;
    let congr_x_fv = 92_406;
    let trans_x_fv = 92_407;

    let alpha = kernel.fvar(alpha_fv);
    let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
    let nat_const = kernel.const_(nat.nat, vec![]);
    let length_const = kernel.const_(names.length, vec![]);
    let reverse_const = kernel.const_(names.reverse, vec![]);
    let cons_const = kernel.const_(names.cons, vec![zero_lvl]);
    let nil_const_lvl = kernel.const_(names.nil, vec![zero_lvl]);
    let append_const = kernel.const_(names.append, vec![]);
    let length_append_const = kernel.const_(length_append, vec![]);

    let length_of =
        |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, length_const, &[alpha, x]) };
    let reverse_of =
        |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, reverse_const, &[alpha, x]) };

    let p = |k: &mut Kernel, x: ExprId| -> ExprId {
        let rev_x = reverse_of(k, x);
        let lhs = length_of(k, rev_x);
        let rhs = length_of(k, x);
        eq_of(k, logic, one_lvl, nat_const, lhs, rhs)
    };
    let base = |k: &mut Kernel| -> ExprId {
        let zero_const = k.const_(nat.zero, vec![]);
        refl_of(k, logic, one_lvl, nat_const, zero_const)
    };
    // length_append instance: length (append (reverse tail) singleton)
    //   = length (reverse tail) + length singleton
    // congr via ih: length (reverse tail) + length singleton
    //   = length tail + length singleton
    // -- both ends (`length (cons head tail)` -> `succ (length tail)` and
    // `add (length tail) (length singleton)` -> `succ (length tail)`, since
    // `length singleton` reduces to the literal `1`) bridged by defeq.
    let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
        let nil_alpha = k.app(nil_const_lvl, alpha);
        let singleton = apply_all(k, cons_const, &[alpha, head, nil_alpha]);
        let add_const = k.const_(nat.add, vec![]);

        let rev_tail = reverse_of(k, tail);
        let append_revtail_singleton = apply_all(k, append_const, &[alpha, rev_tail, singleton]);
        let length_append_revtail_singleton = length_of(k, append_revtail_singleton);
        let length_rev_tail = length_of(k, rev_tail);
        let length_tail = length_of(k, tail);
        let length_singleton = length_of(k, singleton);

        let h1 = apply_all(k, length_append_const, &[alpha, rev_tail, singleton]);
        let h2 = congr_of(
            k,
            logic,
            one_lvl,
            nat_const,
            one_lvl,
            nat_const,
            length_rev_tail,
            length_tail,
            ih,
            congr_x_fv,
            &|k2, x| apply_all(k2, add_const, &[x, length_singleton]),
        );

        let a_full = length_append_revtail_singleton;
        let b_full = apply_all(k, add_const, &[length_rev_tail, length_singleton]);
        let c_full = apply_all(k, add_const, &[length_tail, length_singleton]);
        trans_of(
            k, logic, one_lvl, nat_const, a_full, b_full, c_full, h1, h2, trans_x_fv,
        )
    };
    let target = kernel.fvar(l_fv);
    let proof = list_induct_prop(
        kernel, names, alpha, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
    );
    let concl_ty = p(kernel, target);
    let value = {
        let with_l = lam_fvar(kernel, l_fv, list_alpha, proof, BinderInfo::Default);
        lam_fvar(kernel, alpha_fv, type0, with_l, BinderInfo::Implicit)
    };
    let ty = {
        let with_l = pi_fvar(kernel, l_fv, list_alpha, concl_ty, BinderInfo::Default);
        pi_fvar(kernel, alpha_fv, type0, with_l, BinderInfo::Implicit)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `∀ l z, List.foldr Nat.add z l = List.sum l + z`.
#[allow(clippy::too_many_arguments)]
fn declare_foldr_add_eq_sum_add(
    kernel: &mut Kernel,
    logic: &crate::LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    sum: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "foldrAddEqSumAdd");
    let l_fv = 92_500;
    let z_fv = 92_501;
    let head_fv = 92_502;
    let tail_fv = 92_503;
    let ih_fv = 92_504;
    let x_fv = 92_505;
    let symm_x_fv = 92_506;
    let congr_x_fv = 92_507;
    let trans_x_fv = 92_508;

    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let z = kernel.fvar(z_fv);
    let foldr_const = kernel.const_(names.foldr, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let sum_const = kernel.const_(sum, vec![]);
    let zero_add_const = kernel.const_(nat.zero_add, vec![]);
    let add_assoc_const = kernel.const_(nat.add_assoc, vec![]);

    let foldr_of = |k: &mut Kernel, x: ExprId| -> ExprId {
        apply_all(k, foldr_const, &[nat_const, nat_const, add_const, z, x])
    };
    let sum_of = |k: &mut Kernel, x: ExprId| -> ExprId { k.app(sum_const, x) };

    let p = |k: &mut Kernel, x: ExprId| -> ExprId {
        let lhs = foldr_of(k, x);
        let sum_x = sum_of(k, x);
        let rhs = apply_all(k, add_const, &[sum_x, z]);
        eq_of(k, logic, one_lvl, nat_const, lhs, rhs)
    };
    let base = |k: &mut Kernel| -> ExprId {
        let zero_expr = k.const_(nat.zero, vec![]);
        let add0z = apply_all(k, add_const, &[zero_expr, z]);
        let za = apply_all(k, zero_add_const, &[z]);
        symm_of(k, logic, one_lvl, nat_const, add0z, z, za, symm_x_fv)
    };
    // ih : foldr add z tail = sum tail + z
    // need: foldr add z (cons head tail) = sum (cons head tail) + z
    //   a := add head (foldr add z tail)          [LHS, defeq]
    //   b := add head (add (sum tail) z)           [congr via ih: Eq a b]
    //   c := add (add head (sum tail)) z           [RHS, defeq; add_assoc: Eq c b]
    let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
        let foldr_tail = foldr_of(k, tail);
        let sum_tail = sum_of(k, tail);
        let add_sumtail_z = apply_all(k, add_const, &[sum_tail, z]);
        let a = apply_all(k, add_const, &[head, foldr_tail]);
        let b = apply_all(k, add_const, &[head, add_sumtail_z]);

        let h_congr = congr_of(
            k,
            logic,
            one_lvl,
            nat_const,
            one_lvl,
            nat_const,
            foldr_tail,
            add_sumtail_z,
            ih,
            congr_x_fv,
            &|k2, x| apply_all(k2, add_const, &[head, x]),
        );

        let add_head_sumtail = apply_all(k, add_const, &[head, sum_tail]);
        let c = apply_all(k, add_const, &[add_head_sumtail, z]);
        // add_assoc(head, sum tail, z) : add (add head (sum tail)) z
        //                                  = add head (add (sum tail) z)
        // i.e. Eq c b directly -- no symm needed for THIS leg, but trans_of
        // needs Eq b c, so this one IS reversed.
        let assoc = apply_all(k, add_assoc_const, &[head, sum_tail, z]);
        let b_eq_c = symm_of(k, logic, one_lvl, nat_const, c, b, assoc, symm_x_fv + 1);

        trans_of(
            k, logic, one_lvl, nat_const, a, b, c, h_congr, b_eq_c, trans_x_fv,
        )
    };
    let target = kernel.fvar(l_fv);
    let proof = list_induct_prop(
        kernel, names, nat_const, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
    );
    let concl_ty = p(kernel, target);
    let value = {
        let with_z = lam_fvar(kernel, z_fv, nat_const, proof, BinderInfo::Default);
        lam_fvar(kernel, l_fv, list_nat, with_z, BinderInfo::Default)
    };
    let ty = {
        let with_z = pi_fvar(kernel, z_fv, nat_const, concl_ty, BinderInfo::Default);
        pi_fvar(kernel, l_fv, list_nat, with_z, BinderInfo::Default)
    };
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// `∀ l1 l2, List.sum (List.append l1 l2) = List.sum l1 + List.sum l2`.
///
/// `h1` is `List.foldr_append` instantiated at `(α := Nat, β := Nat,
/// f := Nat.add, z := Nat.zero, l1, l2)`; `h2` is `foldr_add_eq_sum_add`
/// instantiated at `(l1, sum l2)`. Both ends of the chain (`sum … ≡ foldr
/// add 0 …` and `foldr add (foldr add 0 l2) l1 ≡ foldr add (sum l2) l1`) are
/// bridged by defeq, since `sum` unfolds to `foldr add 0`.
#[allow(clippy::too_many_arguments)]
fn declare_sum_append(
    kernel: &mut Kernel,
    logic: &crate::LogicPrelude,
    nat: &NatPrelude,
    names: &ListNames,
    sum: NameId,
    foldr_append: NameId,
    foldr_add_eq_sum_add: NameId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
) -> Result<NameId, KernelError> {
    let name = kernel.name_str(names.list, "sum_append");
    let l1_fv = 92_600;
    let l2_fv = 92_601;
    let trans_x_fv = 92_602;

    let nat_const = kernel.const_(nat.nat, vec![]);
    let list_nat = list_of(kernel, names.list, zero_lvl, nat_const);
    let l1 = kernel.fvar(l1_fv);
    let l2 = kernel.fvar(l2_fv);
    let append_const = kernel.const_(names.append, vec![]);
    let sum_const = kernel.const_(sum, vec![]);
    let add_const = kernel.const_(nat.add, vec![]);
    let zero_const = kernel.const_(nat.zero, vec![]);
    let foldr_const = kernel.const_(names.foldr, vec![]);
    let foldr_append_const = kernel.const_(foldr_append, vec![]);
    let foldr_add_eq_sum_add_const = kernel.const_(foldr_add_eq_sum_add, vec![]);

    let append_l1_l2 = apply_all(kernel, append_const, &[nat_const, l1, l2]);
    let sum_l2 = kernel.app(sum_const, l2);
    let sum_l1 = kernel.app(sum_const, l1);

    let h1 = apply_all(
        kernel,
        foldr_append_const,
        &[nat_const, nat_const, add_const, zero_const, l1, l2],
    );
    let h2 = apply_all(kernel, foldr_add_eq_sum_add_const, &[l1, sum_l2]);

    let a = kernel.app(sum_const, append_l1_l2);
    let b = apply_all(
        kernel,
        foldr_const,
        &[nat_const, nat_const, add_const, sum_l2, l1],
    );
    let c = apply_all(kernel, add_const, &[sum_l1, sum_l2]);
    let proof = trans_of(
        kernel, logic, one_lvl, nat_const, a, b, c, h1, h2, trans_x_fv,
    );

    let concl_ty = eq_of(kernel, logic, one_lvl, nat_const, a, c);
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

/// `∀ a l, List.count a l = Nat.Multiset.count (List.toMultiset l) a`.
///
/// Attempted, not yet landed: the `cons` case needs a case split on
/// `Nat.beq head a` (the same test `List.count`'s own fold already
/// performs) and, in the `false` branch, a bridge from `Nat.beq head a =
/// false` to `head ≠ a` to invoke `Nat.Multiset.count_singleton_of_ne`. See
/// `docs/plan/status/460-list-carrier-1.md` for what is missing and where.
#[allow(clippy::too_many_arguments, dead_code)]
fn declare_count_to_multiset(
    _kernel: &mut Kernel,
    _logic: &crate::LogicPrelude,
    _nat: &NatPrelude,
    _names: &ListNames,
    count: NameId,
    _to_multiset: NameId,
    _zero_lvl: LevelId,
) -> Result<NameId, KernelError> {
    // Not landed -- see the module doc; the caller `.ok()`s this.
    Err(KernelError::PreludePackageConflict { name: count })
}

#[cfg(test)]
mod bridge_tests;
