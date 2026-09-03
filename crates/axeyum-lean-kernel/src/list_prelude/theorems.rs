//! The `List` theorems that need nothing beyond `List` and `Eq` — no
//! `Nat.add`, so no dependence on `build_nat_prelude`. See
//! `super::bridge` for `length_append`/`sum_append`, which do.
//!
//! Every proof here follows the same two-part shape `nat_prelude`'s own
//! documentation describes for `Nat.add`/`Nat.mul`: because `List.append`,
//! `List.map`, `List.foldr` and `List.reverse` all recurse on their FIRST
//! (or only) list argument via `List.rec`, the defining equations at a
//! `nil`/`cons` skeleton hold by ι-reduction alone — no equation lemma is
//! ever needed, only [`ops::congr_of`] to lift an induction hypothesis
//! through the constructor the recursor already exposed. Each proof states
//! explicitly, in its own doc comment, whether its `nil`/base case is
//! `Eq.refl` (both sides collapse to the identical term by defeq) or a real
//! step, per `kernel-proof-engineering.md`'s "before assuming a defeq, check
//! which argument the definition recurses on" rule.

// Proof scripts are long, straight-line term constructions with short
// mathematical names (`a`, `b`, `c`, `p`, `f`, `z`), and every helper is
// imported from `ops` deliberately -- see that module's own doc.
#![allow(clippy::many_single_char_names, clippy::wildcard_imports)]

use super::ListNames;
use super::ops::*;
use crate::LogicPrelude;
use crate::env::Declaration;
use crate::expr::ExprId;
use crate::level::LevelId;
use crate::{BinderInfo, Kernel, KernelError, NameId};

#[allow(clippy::too_many_lines)]
pub(super) fn declare_list_theorems(
    kernel: &mut Kernel,
    logic: &LogicPrelude,
    names: &ListNames,
    zero_lvl: LevelId,
    one_lvl: LevelId,
    type0: ExprId,
) -> Result<(NameId, NameId, NameId, NameId, NameId, NameId), KernelError> {
    let zero = kernel.level_zero();

    // ---------------------------------------------------------------
    // append_assoc : ∀ {α} l1 l2 l3, append (append l1 l2) l3 = append l1 (append l2 l3)
    //
    // nil case is Eq.refl: `append (append nil l2) l3` and
    // `append nil (append l2 l3)` both collapse, by ι alone, to
    // `append l2 l3`.
    // ---------------------------------------------------------------
    let append_assoc = {
        let name = kernel.name_str(names.list, "append_assoc");
        let alpha_fv = 91_000;
        let l1_fv = 91_001;
        let l2_fv = 91_002;
        let l3_fv = 91_003;
        let head_fv = 91_004;
        let tail_fv = 91_005;
        let ih_fv = 91_006;
        let x_fv = 91_007;
        let congr_x_fv = 91_008;

        let alpha = kernel.fvar(alpha_fv);
        let l2 = kernel.fvar(l2_fv);
        let l3 = kernel.fvar(l3_fv);
        let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
        let append_const = kernel.const_(names.append, vec![]);
        let cons_const = kernel.const_(names.cons, vec![zero_lvl]);

        let p = |k: &mut Kernel, x: ExprId| -> ExprId {
            let append_x_l2 = apply_all(k, append_const, &[alpha, x, l2]);
            let lhs = apply_all(k, append_const, &[alpha, append_x_l2, l3]);
            let append_l2_l3 = apply_all(k, append_const, &[alpha, l2, l3]);
            let rhs = apply_all(k, append_const, &[alpha, x, append_l2_l3]);
            eq_of(k, logic, one_lvl, list_alpha, lhs, rhs)
        };
        // Retired to `simp::list` (ADR-1591): `p(nil)` is
        // `Eq (append (append nil l2) l3) (append nil (append l2 l3))`,
        // reachable from `nil_append` alone (a defining-equation refl rule,
        // no `NameId` dependency, so usable even though `append_nil` etc.
        // do not exist as declared names yet at this point in the build):
        // LHS's inner `append nil l2` rewrites to `l2` (lifted through the
        // outer `append _ l3`), RHS's own `append nil (append l2 l3)`
        // rewrites directly to `append l2 l3` -- both converge.
        let base = |k: &mut Kernel| -> ExprId {
            let nil = nil_of(k, names.nil, zero_lvl, alpha);
            let lhs_lit = {
                let inner = apply_all(k, append_const, &[alpha, nil, l2]);
                apply_all(k, append_const, &[alpha, inner, l3])
            };
            let rhs_lit = {
                let l2_l3 = apply_all(k, append_const, &[alpha, l2, l3]);
                apply_all(k, append_const, &[alpha, nil, l2_l3])
            };
            let mut d = crate::simp::list::ListDev::new_list_only(k, logic, names, alpha);
            let rules = vec![crate::simp::list::rule_nil_append()];
            crate::simp::list::prove_eq(&mut d, &rules, list_alpha, lhs_lit, rhs_lit)
                .unwrap_or_else(|e| panic!("append_assoc base case: simp::list declined: {e:?}"))
        };
        let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
            let append_tail_l2 = apply_all(k, append_const, &[alpha, tail, l2]);
            let a = apply_all(k, append_const, &[alpha, append_tail_l2, l3]);
            let append_l2_l3 = apply_all(k, append_const, &[alpha, l2, l3]);
            let b = apply_all(k, append_const, &[alpha, tail, append_l2_l3]);
            congr_of(
                k,
                logic,
                one_lvl,
                list_alpha,
                one_lvl,
                list_alpha,
                a,
                b,
                ih,
                congr_x_fv,
                &|k2, x| apply_all(k2, cons_const, &[alpha, head, x]),
            )
        };
        let target = kernel.fvar(l1_fv);
        let proof = list_induct_prop(
            kernel, names, alpha, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
        );
        let concl_ty = p(kernel, target);
        let value = {
            let with_l3 = lam_fvar(kernel, l3_fv, list_alpha, proof, BinderInfo::Default);
            let with_l2 = lam_fvar(kernel, l2_fv, list_alpha, with_l3, BinderInfo::Default);
            let with_l1 = lam_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
            lam_fvar(kernel, alpha_fv, type0, with_l1, BinderInfo::Implicit)
        };
        let ty = {
            let with_l3 = pi_fvar(kernel, l3_fv, list_alpha, concl_ty, BinderInfo::Default);
            let with_l2 = pi_fvar(kernel, l2_fv, list_alpha, with_l3, BinderInfo::Default);
            let with_l1 = pi_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
            pi_fvar(kernel, alpha_fv, type0, with_l1, BinderInfo::Implicit)
        };
        kernel.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        name
    };

    // ---------------------------------------------------------------
    // append_nil : ∀ {α} l, append l nil = l
    //
    // nil case is Eq.refl: `append nil nil` ι-reduces directly to `nil`.
    // ---------------------------------------------------------------
    let append_nil = {
        let name = kernel.name_str(names.list, "append_nil");
        let alpha_fv = 91_100;
        let l_fv = 91_101;
        let head_fv = 91_102;
        let tail_fv = 91_103;
        let ih_fv = 91_104;
        let x_fv = 91_105;
        let congr_x_fv = 91_106;

        let alpha = kernel.fvar(alpha_fv);
        let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
        let nil_alpha = {
            let c = kernel.const_(names.nil, vec![zero_lvl]);
            kernel.app(c, alpha)
        };
        let append_const = kernel.const_(names.append, vec![]);
        let cons_const = kernel.const_(names.cons, vec![zero_lvl]);

        let p = |k: &mut Kernel, x: ExprId| -> ExprId {
            let ax = apply_all(k, append_const, &[alpha, x, nil_alpha]);
            eq_of(k, logic, one_lvl, list_alpha, ax, x)
        };
        // Retired to `simp::list` (ADR-1591): `p(nil)` is
        // `Eq (append nil nil) nil`, one `nil_append` step.
        let base = |k: &mut Kernel| -> ExprId {
            let lhs_lit = apply_all(k, append_const, &[alpha, nil_alpha, nil_alpha]);
            let mut d = crate::simp::list::ListDev::new_list_only(k, logic, names, alpha);
            let rules = vec![crate::simp::list::rule_nil_append()];
            crate::simp::list::prove_eq(&mut d, &rules, list_alpha, lhs_lit, nil_alpha)
                .unwrap_or_else(|e| panic!("append_nil base case: simp::list declined: {e:?}"))
        };
        let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
            let append_tail_nil = apply_all(k, append_const, &[alpha, tail, nil_alpha]);
            congr_of(
                k,
                logic,
                one_lvl,
                list_alpha,
                one_lvl,
                list_alpha,
                append_tail_nil,
                tail,
                ih,
                congr_x_fv,
                &|k2, x| apply_all(k2, cons_const, &[alpha, head, x]),
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
        name
    };

    // ---------------------------------------------------------------
    // reverse_append (internal lemma `reverse_reverse` needs):
    //   ∀ {α} a b, reverse (append a b) = append (reverse b) (reverse a)
    //
    // nil case: `reverse (append nil b) = append (reverse b) (reverse nil)`
    // reduces (defeq) to `reverse b = append (reverse b) nil`, i.e. exactly
    // `symm (append_nil (reverse b))` — a REAL step, not `Eq.refl`.
    // ---------------------------------------------------------------
    let reverse_append = {
        let name = kernel.name_str(names.list, "reverse_append");
        let alpha_fv = 91_200;
        let a_fv = 91_201;
        let b_fv = 91_202;
        let head_fv = 91_203;
        let tail_fv = 91_204;
        let ih_fv = 91_205;
        let x_fv = 91_206;
        let congr_x_fv = 91_207;
        let trans_x_fv = 91_209;

        let alpha = kernel.fvar(alpha_fv);
        let b = kernel.fvar(b_fv);
        let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
        let append_const = kernel.const_(names.append, vec![]);
        let cons_const = kernel.const_(names.cons, vec![zero_lvl]);
        let reverse_const = kernel.const_(names.reverse, vec![]);
        let append_assoc_const = kernel.const_(append_assoc, vec![]);

        let reverse_of =
            |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, reverse_const, &[alpha, x]) };
        let append_of = |k: &mut Kernel, x: ExprId, y: ExprId| -> ExprId {
            apply_all(k, append_const, &[alpha, x, y])
        };

        let p = |k: &mut Kernel, x: ExprId| -> ExprId {
            let append_x_b = append_of(k, x, b);
            let lhs = reverse_of(k, append_x_b);
            let rev_b = reverse_of(k, b);
            let rev_x = reverse_of(k, x);
            let rhs = append_of(k, rev_b, rev_x);
            eq_of(k, logic, one_lvl, list_alpha, lhs, rhs)
        };
        // Retired to `simp::list` (ADR-1591): `p(nil)` is
        // `Eq (reverse (append nil b)) (append (reverse b) (reverse nil))`.
        // LHS: `append nil b` rewrites (`nil_append`) to `b`, lifted through
        // the outer `reverse`. RHS: `reverse nil` rewrites (`reverse_nil`)
        // to `nil`, then `append (reverse b) nil` rewrites (`append_nil`,
        // NOW a declared name -- this theorem runs after it) to
        // `reverse b`. Both converge to `reverse b`.
        let base = |k: &mut Kernel| -> ExprId {
            let rev_b = reverse_of(k, b);
            let nil_c = k.const_(names.nil, vec![zero_lvl]);
            let nil_alpha = k.app(nil_c, alpha);
            let nil_b = append_of(k, nil_alpha, b);
            let lhs_lit = reverse_of(k, nil_b);
            let rev_nil = reverse_of(k, nil_alpha);
            let rhs_lit = append_of(k, rev_b, rev_nil);
            let mut d = crate::simp::list::ListDev::new_list_only(k, logic, names, alpha);
            let rules = vec![
                crate::simp::list::rule_nil_append(),
                crate::simp::list::rule_append_nil(append_nil),
                crate::simp::list::rule_reverse_nil(),
            ];
            crate::simp::list::prove_eq(&mut d, &rules, list_alpha, lhs_lit, rhs_lit)
                .unwrap_or_else(|e| panic!("reverse_append base case: simp::list declined: {e:?}"))
        };
        // ih : reverse (append tail b) = append (reverse b) (reverse tail)
        // need: reverse (append (cons head tail) b)
        //         = append (reverse b) (reverse (cons head tail))
        //
        // LHS ≡ reverse (cons head (append tail b))
        //     ≡ append (reverse (append tail b)) (cons head nil)   [defeq]
        // by ih (congr on `append _ (cons head nil)`):
        //     = append (append (reverse b) (reverse tail)) (cons head nil)
        // by append_assoc:
        //     = append (reverse b) (append (reverse tail) (cons head nil))
        // RHS ≡ append (reverse b) (reverse (cons head tail))
        //     ≡ append (reverse b) (append (reverse tail) (cons head nil))  [defeq]
        // so the two chained steps suffice, ends bridged by defeq.
        let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
            let rev_b = reverse_of(k, b);
            let rev_tail = reverse_of(k, tail);
            let nil_c = k.const_(names.nil, vec![zero_lvl]);
            let nil_alpha = k.app(nil_c, alpha);
            let singleton = apply_all(k, cons_const, &[alpha, head, nil_alpha]);

            let append_tail_b = append_of(k, tail, b);
            let rev_append_tail_b = reverse_of(k, append_tail_b);
            let mid_a = append_of(k, rev_b, rev_tail);

            let step1 = congr_of(
                k,
                logic,
                one_lvl,
                list_alpha,
                one_lvl,
                list_alpha,
                rev_append_tail_b,
                mid_a,
                ih,
                congr_x_fv,
                &|k2, x| apply_all(k2, append_const, &[alpha, x, singleton]),
            );
            let assoc_instance =
                apply_all(k, append_assoc_const, &[alpha, rev_b, rev_tail, singleton]);

            let a_full = apply_all(k, append_const, &[alpha, rev_append_tail_b, singleton]);
            let b_full = apply_all(k, append_const, &[alpha, mid_a, singleton]);
            let rev_tail_singleton = apply_all(k, append_const, &[alpha, rev_tail, singleton]);
            let c_full = apply_all(k, append_const, &[alpha, rev_b, rev_tail_singleton]);

            trans_of(
                k,
                logic,
                one_lvl,
                list_alpha,
                a_full,
                b_full,
                c_full,
                step1,
                assoc_instance,
                trans_x_fv,
            )
        };
        let target = kernel.fvar(a_fv);
        let proof = list_induct_prop(
            kernel, names, alpha, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
        );
        let concl_ty = p(kernel, target);
        let value = {
            let with_b = lam_fvar(kernel, b_fv, list_alpha, proof, BinderInfo::Default);
            let with_a = lam_fvar(kernel, a_fv, list_alpha, with_b, BinderInfo::Default);
            lam_fvar(kernel, alpha_fv, type0, with_a, BinderInfo::Implicit)
        };
        let ty = {
            let with_b = pi_fvar(kernel, b_fv, list_alpha, concl_ty, BinderInfo::Default);
            let with_a = pi_fvar(kernel, a_fv, list_alpha, with_b, BinderInfo::Default);
            pi_fvar(kernel, alpha_fv, type0, with_a, BinderInfo::Implicit)
        };
        kernel.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        let _ = (one_lvl, zero);
        name
    };

    // ---------------------------------------------------------------
    // reverse_reverse : ∀ {α} l, reverse (reverse l) = l
    // ---------------------------------------------------------------
    let reverse_reverse = {
        let name = kernel.name_str(names.list, "reverse_reverse");
        let alpha_fv = 91_300;
        let l_fv = 91_301;
        let head_fv = 91_302;
        let tail_fv = 91_303;
        let ih_fv = 91_304;
        let x_fv = 91_305;
        let congr_x_fv = 91_306;
        let trans_x_fv = 91_307;

        let alpha = kernel.fvar(alpha_fv);
        let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
        let reverse_const = kernel.const_(names.reverse, vec![]);
        let cons_const = kernel.const_(names.cons, vec![zero_lvl]);
        let nil_const_lvl = kernel.const_(names.nil, vec![zero_lvl]);
        let reverse_append_const = kernel.const_(reverse_append, vec![]);

        let reverse_of =
            |k: &mut Kernel, x: ExprId| -> ExprId { apply_all(k, reverse_const, &[alpha, x]) };

        let p = |k: &mut Kernel, x: ExprId| -> ExprId {
            let rev_x = reverse_of(k, x);
            let rr = reverse_of(k, rev_x);
            eq_of(k, logic, one_lvl, list_alpha, rr, x)
        };
        // Retired to `simp::list` (ADR-1591): `p(nil)` is
        // `Eq (reverse (reverse nil)) nil`, two `reverse_nil` steps (the
        // outer `reverse` still wraps a `reverse nil` redex after the
        // first rewrite peels the inner one).
        let base = |k: &mut Kernel| -> ExprId {
            let nil_alpha = k.app(nil_const_lvl, alpha);
            let rev_nil = reverse_of(k, nil_alpha);
            let lhs_lit = reverse_of(k, rev_nil);
            let mut d = crate::simp::list::ListDev::new_list_only(k, logic, names, alpha);
            let rules = vec![crate::simp::list::rule_reverse_nil()];
            crate::simp::list::prove_eq(&mut d, &rules, list_alpha, lhs_lit, nil_alpha)
                .unwrap_or_else(|e| panic!("reverse_reverse base case: simp::list declined: {e:?}"))
        };
        let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
            let nil_alpha = k.app(nil_const_lvl, alpha);
            let singleton = apply_all(k, cons_const, &[alpha, head, nil_alpha]);
            let append_const = k.const_(names.append, vec![]);

            let rev_tail = reverse_of(k, tail);
            let append_revtail_singleton =
                apply_all(k, append_const, &[alpha, rev_tail, singleton]);
            let reverse_of_that = reverse_of(k, append_revtail_singleton);
            let rev_singleton = reverse_of(k, singleton);
            let rev_rev_tail = reverse_of(k, rev_tail);

            // h1 : reverse (append (reverse tail) singleton)
            //        = append (reverse singleton) (reverse (reverse tail))
            let h1 = apply_all(k, reverse_append_const, &[alpha, rev_tail, singleton]);

            // h2 : append (reverse singleton) (reverse (reverse tail))
            //        = append (reverse singleton) tail            [congr via ih]
            let h2 = congr_of(
                k,
                logic,
                one_lvl,
                list_alpha,
                one_lvl,
                list_alpha,
                rev_rev_tail,
                tail,
                ih,
                congr_x_fv,
                &|k2, x| apply_all(k2, append_const, &[alpha, rev_singleton, x]),
            );

            let a_full = reverse_of_that;
            let b_full = apply_all(k, append_const, &[alpha, rev_singleton, rev_rev_tail]);
            let c_full = apply_all(k, append_const, &[alpha, rev_singleton, tail]);

            trans_of(
                k, logic, one_lvl, list_alpha, a_full, b_full, c_full, h1, h2, trans_x_fv,
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
        name
    };

    // ---------------------------------------------------------------
    // length_map : ∀ {α β} f l, length (map f l) = length l
    //
    // nil case is Eq.refl: both sides ι-reduce to `Nat.zero`.
    // ---------------------------------------------------------------
    let length_map = {
        let name = kernel.name_str(names.list, "length_map");
        let alpha_fv = 91_400;
        let beta_fv = 91_401;
        let f_fv = 91_402;
        let l_fv = 91_403;
        let head_fv = 91_404;
        let tail_fv = 91_405;
        let ih_fv = 91_406;
        let x_fv = 91_407;
        let congr_x_fv = 91_408;

        let alpha = kernel.fvar(alpha_fv);
        let beta = kernel.fvar(beta_fv);
        let f = kernel.fvar(f_fv);
        let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
        let f_ty = arrow(kernel, alpha, beta);
        let map_const = kernel.const_(names.map, vec![]);
        let length_const = kernel.const_(names.length, vec![]);
        let nat_const = kernel.const_(logic.nat, vec![]);
        let succ_const = kernel.const_(logic.nat_succ, vec![]);

        let p = |k: &mut Kernel, x: ExprId| -> ExprId {
            let mapped = apply_all(k, map_const, &[alpha, beta, f, x]);
            let lhs = apply_all(k, length_const, &[beta, mapped]);
            let rhs = apply_all(k, length_const, &[alpha, x]);
            eq_of(k, logic, one_lvl, nat_const, lhs, rhs)
        };
        // Retired to `simp::list` (ADR-1591): `p(nil)` is
        // `Eq (length (map f nil)) (length nil)`. LHS: `map f nil`
        // rewrites (`map_nil`) to `nil` (at `beta`), lifted through the
        // outer `length`, then `length nil` rewrites (`length_nil`) to
        // `zero`. RHS: `length nil` rewrites (`length_nil`) to `zero`
        // directly. `map_nil`'s result carrier is `List beta`, not `List
        // alpha` -- `d.set_beta(beta)` before proving, since `alpha` and
        // `beta` are genuinely different type variables here (unlike every
        // other retirement in this file, which stays at one `alpha`).
        let base = |k: &mut Kernel| -> ExprId {
            let nil_alpha = nil_of(k, names.nil, zero_lvl, alpha);
            let mapped_nil = apply_all(k, map_const, &[alpha, beta, f, nil_alpha]);
            let lhs_lit = apply_all(k, length_const, &[beta, mapped_nil]);
            let rhs_lit = apply_all(k, length_const, &[alpha, nil_alpha]);
            let mut d = crate::simp::list::ListDev::new_list_only(k, logic, names, alpha);
            d.set_beta(beta);
            let rules = vec![
                crate::simp::list::rule_map_nil(),
                crate::simp::list::rule_length_nil(),
            ];
            crate::simp::list::prove_eq(&mut d, &rules, nat_const, lhs_lit, rhs_lit)
                .unwrap_or_else(|e| panic!("length_map base case: simp::list declined: {e:?}"))
        };
        let step = |k: &mut Kernel, _head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
            let mapped_tail = apply_all(k, map_const, &[alpha, beta, f, tail]);
            let a = apply_all(k, length_const, &[beta, mapped_tail]);
            let b = apply_all(k, length_const, &[alpha, tail]);
            congr_of(
                k,
                logic,
                one_lvl,
                nat_const,
                one_lvl,
                nat_const,
                a,
                b,
                ih,
                congr_x_fv,
                &|k2, x| k2.app(succ_const, x),
            )
        };
        let target = kernel.fvar(l_fv);
        let proof = list_induct_prop(
            kernel, names, alpha, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
        );
        let concl_ty = p(kernel, target);
        let value = {
            let with_l = lam_fvar(kernel, l_fv, list_alpha, proof, BinderInfo::Default);
            let with_f = lam_fvar(kernel, f_fv, f_ty, with_l, BinderInfo::Default);
            let with_beta = lam_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
            lam_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
        };
        let ty = {
            let with_l = pi_fvar(kernel, l_fv, list_alpha, concl_ty, BinderInfo::Default);
            let with_f = pi_fvar(kernel, f_fv, f_ty, with_l, BinderInfo::Default);
            let with_beta = pi_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
            pi_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
        };
        kernel.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        name
    };

    // ---------------------------------------------------------------
    // foldr_append : ∀ {α β} f z l1 l2,
    //   foldr f z (append l1 l2) = foldr f (foldr f z l2) l1
    //
    // nil case is Eq.refl: both sides ι-reduce to `foldr f z l2`.
    // ---------------------------------------------------------------
    let foldr_append = {
        let name = kernel.name_str(names.list, "foldr_append");
        let alpha_fv = 91_500;
        let beta_fv = 91_501;
        let f_fv = 91_502;
        let z_fv = 91_503;
        let l1_fv = 91_504;
        let l2_fv = 91_505;
        let head_fv = 91_506;
        let tail_fv = 91_507;
        let ih_fv = 91_508;
        let x_fv = 91_509;
        let congr_x_fv = 91_510;

        let alpha = kernel.fvar(alpha_fv);
        let beta = kernel.fvar(beta_fv);
        let f = kernel.fvar(f_fv);
        let z = kernel.fvar(z_fv);
        let l2 = kernel.fvar(l2_fv);
        let list_alpha = list_of(kernel, names.list, zero_lvl, alpha);
        let f_ty = {
            let inner = arrow(kernel, beta, beta);
            arrow(kernel, alpha, inner)
        };
        let append_const = kernel.const_(names.append, vec![]);
        let foldr_const = kernel.const_(names.foldr, vec![]);

        let p = |k: &mut Kernel, x: ExprId| -> ExprId {
            let append_x_l2 = apply_all(k, append_const, &[alpha, x, l2]);
            let lhs = apply_all(k, foldr_const, &[alpha, beta, f, z, append_x_l2]);
            let foldr_z_l2 = apply_all(k, foldr_const, &[alpha, beta, f, z, l2]);
            let rhs = apply_all(k, foldr_const, &[alpha, beta, f, foldr_z_l2, x]);
            eq_of(k, logic, one_lvl, beta, lhs, rhs)
        };
        let base = |k: &mut Kernel| -> ExprId {
            let foldr_z_l2 = apply_all(k, foldr_const, &[alpha, beta, f, z, l2]);
            refl_of(k, logic, one_lvl, beta, foldr_z_l2)
        };
        let step = |k: &mut Kernel, head: ExprId, tail: ExprId, ih: ExprId| -> ExprId {
            let append_tail_l2 = apply_all(k, append_const, &[alpha, tail, l2]);
            let a = apply_all(k, foldr_const, &[alpha, beta, f, z, append_tail_l2]);
            let foldr_z_l2 = apply_all(k, foldr_const, &[alpha, beta, f, z, l2]);
            let b = apply_all(k, foldr_const, &[alpha, beta, f, foldr_z_l2, tail]);
            congr_of(
                k,
                logic,
                one_lvl,
                beta,
                one_lvl,
                beta,
                a,
                b,
                ih,
                congr_x_fv,
                &|k2, x| {
                    let fh = k2.app(f, head);
                    k2.app(fh, x)
                },
            )
        };
        let target = kernel.fvar(l1_fv);
        let proof = list_induct_prop(
            kernel, names, alpha, zero_lvl, &p, &base, &step, target, x_fv, head_fv, tail_fv, ih_fv,
        );
        let concl_ty = p(kernel, target);
        // Outer-to-inner (i.e. application) order is alpha, beta, f, z, l1,
        // l2 — l2 is wrapped FIRST (innermost) so l1 ends up as the first
        // explicit argument, matching the doc comment above and
        // `append_assoc`'s convention.
        let value = {
            let with_l2 = lam_fvar(kernel, l2_fv, list_alpha, proof, BinderInfo::Default);
            let with_l1 = lam_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
            let with_z = lam_fvar(kernel, z_fv, beta, with_l1, BinderInfo::Default);
            let with_f = lam_fvar(kernel, f_fv, f_ty, with_z, BinderInfo::Default);
            let with_beta = lam_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
            lam_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
        };
        let ty = {
            let with_l2 = pi_fvar(kernel, l2_fv, list_alpha, concl_ty, BinderInfo::Default);
            let with_l1 = pi_fvar(kernel, l1_fv, list_alpha, with_l2, BinderInfo::Default);
            let with_z = pi_fvar(kernel, z_fv, beta, with_l1, BinderInfo::Default);
            let with_f = pi_fvar(kernel, f_fv, f_ty, with_z, BinderInfo::Default);
            let with_beta = pi_fvar(kernel, beta_fv, type0, with_f, BinderInfo::Implicit);
            pi_fvar(kernel, alpha_fv, type0, with_beta, BinderInfo::Implicit)
        };
        kernel.add_declaration(Declaration::Theorem {
            name,
            uparams: vec![],
            ty,
            value,
        })?;
        name
    };

    // `length_append` and `length_reverse` both need `Nat.zero_add`/
    // `Nat.succ_add` (real theorems, since our `Nat.add` recurses on its
    // RIGHT argument and so does not reduce `0 + x`/`succ a + x` for a
    // symbolic `x` by defeq alone) — so both are declared in `super::bridge`,
    // after `build_nat_prelude`, rather than here.
    Ok((
        append_assoc,
        append_nil,
        reverse_append,
        reverse_reverse,
        length_map,
        foldr_append,
    ))
}
