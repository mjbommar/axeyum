//! **Slice 7 of the first-order model theory group** (`fo_*.rs`, ADR-1640):
//! the Gödel numbering itself — `FO.Term.code`, `FO.Formula.code`, and the
//! injectivity of both.
//!
//! ```text
//! FO.Term.code    : FO.Term    -> Nat
//! FO.Formula.code : FO.Formula -> Nat
//!
//! FO.Term.code_injective    : Π t u, Eq Nat (Term.code t)    (Term.code u)    -> Eq FO.Term t u
//! FO.Formula.code_injective : Π p q, Eq Nat (Formula.code p) (Formula.code q) -> Eq FO.Formula p q
//! ```
//!
//! ## The encoding
//!
//! Every constructor is `FO.Code.pair tag payload` with a distinct tag, and
//! the payload nests the field codes to the right:
//!
//! ```text
//! Term.var i        ↦ pair 0 i                     Formula.bot        ↦ pair 0 0
//! Term.f0 k         ↦ pair 1 k                     Formula.eqf t u    ↦ pair 1 (pair ⌜t⌝ ⌜u⌝)
//! Term.f1 k t       ↦ pair 2 (pair k ⌜t⌝)          Formula.rel1 k t   ↦ pair 2 (pair k ⌜t⌝)
//! Term.f2 k t u     ↦ pair 3 (pair k               Formula.rel2 k t u ↦ pair 3 (pair k
//!                                (pair ⌜t⌝ ⌜u⌝))                              (pair ⌜t⌝ ⌜u⌝))
//!                                                  Formula.and_ p q   ↦ pair 4 (pair ⌜p⌝ ⌜q⌝)
//!                                                  Formula.or_ p q    ↦ pair 5 (pair ⌜p⌝ ⌜q⌝)
//!                                                  Formula.imp p q    ↦ pair 6 (pair ⌜p⌝ ⌜q⌝)
//!                                                  Formula.all p      ↦ pair 7 ⌜p⌝
//!                                                  Formula.ex p       ↦ pair 8 ⌜p⌝
//! ```
//!
//! The two numberings share `FO.Code.pair`, so a `Term` code and a `Formula`
//! code are the same natural number for different objects — that is harmless
//! and deliberate: injectivity is a statement *within* each type, which is
//! what the diagonal lemma and every representability argument need. A single
//! numbering across both would need a further tag and buys nothing here.
//!
//! Because the pairing is the anti-diagonal enumeration, **small formulas get
//! small codes**: `⌜bot⌝ = 0`, `⌜Formula.all bot⌝ = 35`,
//! `⌜Formula.imp bot bot⌝ = 27`. Every numeral in this kernel is unary, so
//! that matters — a `2^a(2b+1)` style pairing would have put a
//! four-constructor formula out of reach of any evaluation test.
//!
//! ## Injectivity: 16 + 81 cases, in two shapes
//!
//! `code_injective` is a double recursion — an outer structural induction
//! carrying `Π u, Eq Nat (code t) (code u) -> Eq _ t u`, and an inner case
//! analysis on `u`. The off-diagonal cases (12 of 16, 72 of 81) are all one
//! construction: `FO.Code.pair_inj_left` reads the two tags off the
//! hypothesis, and distinct unary numerals are refuted by stripping `succ`s
//! with `Nat.succ_injective` until `Nat.succ_ne_zero` applies. The diagonal
//! cases are the other construction: `pair_inj_left`/`pair_inj_right` peel the
//! payload apart, each component equality is converted (a `Nat` field is
//! already one, a `Term` field goes through `FO.Term.code_injective`, a
//! recursive field goes through the induction hypothesis), and the results are
//! recombined by congruence in one argument at a time.
//!
//! This is the whole reason `fo_code.rs` proves a round trip rather than
//! injectivity directly: with `FO.Code.fst_pair`/`snd_pair` in hand the two
//! projections of the hypothesis are one application each, and neither shape
//! above needs a further induction over `Nat`.

#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::fo_code::{
    CodeNames, build_fo_code_prelude, false_elim, numeral, pair_app, succ_inj, succ_ne_zero_elim,
};
use crate::fo_syntax::{
    apply_all, arrow, gcongr, geq, grefl, gsymm, gtrans, lam_fv, lams, pi_fv, pis,
};
use crate::{
    BinderInfo, Declaration, ExprId, FoCodePrelude, KernelError, LogicPrelude, NameId,
    ReducibilityHint,
};

/// Names produced by [`build_fo_numbering_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoNumberingPrelude {
    /// The pairing this numbering is built out of.
    pub code: FoCodePrelude,
    /// `FO.Term.code : FO.Term -> Nat`.
    pub term_code: NameId,
    /// `FO.Formula.code : FO.Formula -> Nat`.
    pub formula_code: NameId,
    /// `FO.Term.code_injective : Π t u, Eq Nat (code t) (code u) -> Eq FO.Term t u`.
    pub term_code_injective: NameId,
    /// `FO.Formula.code_injective : Π p q, Eq Nat (code p) (code q) -> Eq FO.Formula p q`.
    pub formula_code_injective: NameId,
}

/// What a constructor field contributes, both to the code and to the
/// injectivity argument.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Field {
    /// A `Nat` field (a de Bruijn index or a symbol index): its own code.
    Nat,
    /// An `FO.Term` field of a `Formula` constructor: coded by `FO.Term.code`,
    /// inverted by `FO.Term.code_injective`.
    Term,
    /// A field of the type being recursed on: coded by the recursion, inverted
    /// by the induction hypothesis.
    Rec,
}

/// One constructor of the inductive being numbered.
struct Ctor {
    name: NameId,
    tag: u32,
    fields: &'static [Field],
}

/// A monotone supply of free-variable ids, so that the 97 nested minor
/// premises below cannot collide.
struct Fv(u64);

impl Fv {
    fn next(&mut self) -> u64 {
        self.0 += 1;
        self.0
    }
}

/// Build `FO.Term.code`, `FO.Formula.code` and their injectivity theorems.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_numbering_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoNumberingPrelude, KernelError> {
    let code = build_fo_code_prelude(kernel)?;
    let syntax = code.syntax;
    let c = CodeNames::rebuild(kernel, syntax.nat);
    let term_ty = kernel.const_(syntax.term, vec![]);
    let formula_ty = kernel.const_(syntax.formula, vec![]);

    let term_ctors = vec![
        Ctor {
            name: syntax.var,
            tag: 0,
            fields: &[Field::Nat],
        },
        Ctor {
            name: syntax.f0,
            tag: 1,
            fields: &[Field::Nat],
        },
        Ctor {
            name: syntax.f1,
            tag: 2,
            fields: &[Field::Nat, Field::Rec],
        },
        Ctor {
            name: syntax.f2,
            tag: 3,
            fields: &[Field::Nat, Field::Rec, Field::Rec],
        },
    ];
    let formula_ctors = vec![
        Ctor {
            name: syntax.bot,
            tag: 0,
            fields: &[],
        },
        Ctor {
            name: syntax.eqf,
            tag: 1,
            fields: &[Field::Term, Field::Term],
        },
        Ctor {
            name: syntax.rel1,
            tag: 2,
            fields: &[Field::Nat, Field::Term],
        },
        Ctor {
            name: syntax.rel2,
            tag: 3,
            fields: &[Field::Nat, Field::Term, Field::Term],
        },
        Ctor {
            name: syntax.and_,
            tag: 4,
            fields: &[Field::Rec, Field::Rec],
        },
        Ctor {
            name: syntax.or_,
            tag: 5,
            fields: &[Field::Rec, Field::Rec],
        },
        Ctor {
            name: syntax.imp,
            tag: 6,
            fields: &[Field::Rec, Field::Rec],
        },
        Ctor {
            name: syntax.all,
            tag: 7,
            fields: &[Field::Rec],
        },
        Ctor {
            name: syntax.ex,
            tag: 8,
            fields: &[Field::Rec],
        },
    ];

    let term_code = declare_code(
        kernel,
        &c,
        &term_ctors,
        term_ty,
        term_ty,
        syntax.term_rec,
        syntax.term,
        None,
        &mut Fv(1_641_000),
    )?;
    let formula_code = declare_code(
        kernel,
        &c,
        &formula_ctors,
        formula_ty,
        term_ty,
        syntax.formula_rec,
        syntax.formula,
        Some(term_code),
        &mut Fv(1_642_000),
    )?;

    let term_code_injective = declare_code_injective(
        kernel,
        &c,
        &InjCtx {
            ctors: &term_ctors,
            carrier_ty: term_ty,
            term_ty,
            rec_name: syntax.term_rec,
            namespace: syntax.term,
            code_name: term_code,
            term_code,
            term_code_injective: None,
        },
        &mut Fv(1_643_000),
    )?;
    let formula_code_injective = declare_code_injective(
        kernel,
        &c,
        &InjCtx {
            ctors: &formula_ctors,
            carrier_ty: formula_ty,
            term_ty,
            rec_name: syntax.formula_rec,
            namespace: syntax.formula,
            code_name: formula_code,
            term_code,
            term_code_injective: Some(term_code_injective),
        },
        &mut Fv(1_644_000),
    )?;

    Ok(FoNumberingPrelude {
        code,
        term_code,
        formula_code,
        term_code_injective,
        formula_code_injective,
    })
}

// ============================================================================
// The payload shape, shared by the definition and the injectivity proof.
// ============================================================================

/// `payload [] = 0`, `payload [x] = x`, `payload [x, y] = pair x y`,
/// `payload [x, y, z] = pair x (pair y z)` — nested to the RIGHT, which is
/// what makes the injectivity extraction a fixed sequence of
/// `pair_inj_left` / `pair_inj_right`.
fn payload(kernel: &mut crate::Kernel, c: &CodeNames, codes: &[ExprId]) -> ExprId {
    match codes {
        [] => numeral(kernel, c, 0),
        [x] => *x,
        [x, rest @ ..] => {
            let tail = payload(kernel, c, rest);
            pair_app(kernel, c, *x, tail)
        }
    }
}

/// `FO.Code.pair tag (payload codes)`.
fn tagged(kernel: &mut crate::Kernel, c: &CodeNames, tag: u32, codes: &[ExprId]) -> ExprId {
    let tag_num = numeral(kernel, c, tag);
    let body = payload(kernel, c, codes);
    pair_app(kernel, c, tag_num, body)
}

/// The binder type a field of this kind carries.
fn field_ty(kind: Field, carrier_ty: ExprId, term_ty: ExprId, nat_ty: ExprId) -> ExprId {
    match kind {
        Field::Nat => nat_ty,
        Field::Term => term_ty,
        Field::Rec => carrier_ty,
    }
}

// ============================================================================
// FO.Term.code and FO.Formula.code.
// ============================================================================

/// Declare `<namespace>.code : <carrier> -> Nat` as a recursor application at
/// the non-dependent motive `fun _ => Nat`.
fn declare_code(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    ctors: &[Ctor],
    carrier_ty: ExprId,
    term_ty: ExprId,
    rec_name: NameId,
    namespace: NameId,
    term_code: Option<NameId>,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let nat_ty = c.nat_ty;
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, carrier_ty, nat_ty, BinderInfo::Default)
    };

    let mut minors = vec![motive];
    for ctor in ctors {
        // Field binders, then one induction-hypothesis binder per recursive
        // field, appended in field order (the shape `add_inductive` generates).
        let field_ids: Vec<u64> = ctor.fields.iter().map(|_| fv.next()).collect();
        let ih_ids: Vec<Option<u64>> = ctor
            .fields
            .iter()
            .map(|k| {
                if *k == Field::Rec {
                    Some(fv.next())
                } else {
                    None
                }
            })
            .collect();

        let mut codes = Vec::new();
        for (idx, kind) in ctor.fields.iter().enumerate() {
            let value = match kind {
                Field::Nat => kernel.fvar(field_ids[idx]),
                Field::Term => {
                    let arg = kernel.fvar(field_ids[idx]);
                    let f = kernel.const_(
                        term_code.expect("a Term field needs FO.Term.code declared first"),
                        vec![],
                    );
                    kernel.app(f, arg)
                }
                Field::Rec => kernel.fvar(ih_ids[idx].expect("a recursive field has an IH")),
            };
            codes.push(value);
        }
        let body = tagged(kernel, c, ctor.tag, &codes);

        let mut binders: Vec<(u64, ExprId)> = ctor
            .fields
            .iter()
            .enumerate()
            .map(|(idx, kind)| (field_ids[idx], field_ty(*kind, carrier_ty, term_ty, nat_ty)))
            .collect();
        for id in ih_ids.into_iter().flatten() {
            binders.push((id, nat_ty));
        }
        minors.push(lams(kernel, &binders, body));
    }

    let t_id = fv.next();
    let t = kernel.fvar(t_id);
    let rec = kernel.const_(rec_name, vec![one]);
    let applied = {
        let head = apply_all(kernel, rec, &minors);
        kernel.app(head, t)
    };
    let value = lam_fv(kernel, t_id, carrier_ty, applied);
    let ty = arrow(kernel, carrier_ty, nat_ty);
    let name = kernel.name_str(namespace, "code");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

// ============================================================================
// Injectivity.
// ============================================================================

/// Everything the injectivity builder needs about the inductive it is working
/// over.
struct InjCtx<'a> {
    ctors: &'a [Ctor],
    carrier_ty: ExprId,
    term_ty: ExprId,
    rec_name: NameId,
    namespace: NameId,
    code_name: NameId,
    term_code: NameId,
    term_code_injective: Option<NameId>,
}

/// `<code_name> x`.
fn code_of(kernel: &mut crate::Kernel, code_name: NameId, x: ExprId) -> ExprId {
    let f = kernel.const_(code_name, vec![]);
    kernel.app(f, x)
}

/// A proof of `False` from `h : Eq Nat (numeral i) (numeral j)` with `i != j`:
/// strip `min(i, j)` `succ`s with `Nat.succ_injective`, then apply
/// `Nat.succ_ne_zero` to whichever side is still a `succ`.
fn numeral_ne_absurd(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    logic: LogicPrelude,
    i: u32,
    j: u32,
    h: ExprId,
    fv: &mut Fv,
) -> ExprId {
    assert!(i != j, "numeral_ne_absurd needs two DIFFERENT tags");
    let shared = i.min(j);
    let mut current = h;
    for k in 0..shared {
        let left = numeral(kernel, c, i - k - 1);
        let right = numeral(kernel, c, j - k - 1);
        current = succ_inj(kernel, c, left, right, current);
    }
    // One side is now `Nat.zero`; orient so the `succ` side comes first.
    let (bigger, smaller_is_left) = if i > j { (i - j, true) } else { (j - i, false) };
    let stripped = numeral(kernel, c, bigger - 1);
    let oriented = if smaller_is_left {
        current
    } else {
        let zero = numeral(kernel, c, 0);
        let big = numeral(kernel, c, bigger);
        let id = fv.next();
        gsymm(kernel, logic, c.nat_ty, zero, big, current, id)
    };
    succ_ne_zero_elim(kernel, c, stripped, oriented)
}

/// `Eq dst (build lhs) (build rhs)`, rewritten one argument at a time.
/// `proofs[i]` is `None` exactly when `lhs[i]` and `rhs[i]` are the same term.
fn congr_args(
    kernel: &mut crate::Kernel,
    logic: LogicPrelude,
    dst_ty: ExprId,
    src_tys: &[ExprId],
    lhs_args: &[ExprId],
    rhs_args: &[ExprId],
    proofs: &[Option<ExprId>],
    build: &dyn Fn(&mut crate::Kernel, &[ExprId]) -> ExprId,
    fv: &mut Fv,
) -> ExprId {
    let start = build(kernel, lhs_args);
    let mut current: Vec<ExprId> = lhs_args.to_vec();
    let mut acc = grefl(kernel, logic, dst_ty, start);
    for idx in 0..lhs_args.len() {
        let Some(pf) = proofs[idx] else { continue };
        let before = build(kernel, &current);
        let mut next = current.clone();
        next[idx] = rhs_args[idx];
        let after = build(kernel, &next);
        let step = {
            let context = current.clone();
            let hole = move |kern: &mut crate::Kernel, x: ExprId| -> ExprId {
                let mut args = context.clone();
                args[idx] = x;
                build(kern, &args)
            };
            let id = fv.next();
            gcongr(
                kernel,
                logic,
                src_tys[idx],
                dst_ty,
                current[idx],
                rhs_args[idx],
                pf,
                &hole,
                id,
            )
        };
        let id = fv.next();
        acc = gtrans(kernel, logic, dst_ty, start, before, after, acc, step, id);
        current = next;
    }
    acc
}

/// Split `h : Eq Nat (payload lhs) (payload rhs)` into one equality per
/// component. `payload` nests to the right, so this is a fixed alternation of
/// `pair_inj_left` (take the head) and `pair_inj_right` (descend into the
/// tail).
fn split_payload(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    inj_left: NameId,
    inj_right: NameId,
    lhs: &[ExprId],
    rhs: &[ExprId],
    h: ExprId,
) -> Vec<ExprId> {
    let mut out = Vec::new();
    let mut current = h;
    for idx in 0..lhs.len() {
        if idx + 1 == lhs.len() {
            out.push(current);
            break;
        }
        let ltail = payload(kernel, c, &lhs[idx + 1..]);
        let rtail = payload(kernel, c, &rhs[idx + 1..]);
        let args = [lhs[idx], ltail, rhs[idx], rtail];
        let head = {
            let f = kernel.const_(inj_left, vec![]);
            let applied = apply_all(kernel, f, &args);
            kernel.app(applied, current)
        };
        let tail = {
            let f = kernel.const_(inj_right, vec![]);
            let applied = apply_all(kernel, f, &args);
            kernel.app(applied, current)
        };
        out.push(head);
        current = tail;
    }
    out
}

/// Declare `<namespace>.code_injective`.
fn declare_code_injective(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    ctx: &InjCtx<'_>,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let zero_lvl = kernel.level_zero();
    let logic = c.logic;
    let nat_ty = c.nat_ty;
    let carrier = ctx.carrier_ty;

    // claim t := Π u, Eq Nat (code t) (code u) -> Eq carrier t u
    let claim = |kern: &mut crate::Kernel, t: ExprId, u_id: u64| -> ExprId {
        let u = kern.fvar(u_id);
        let ct = code_of(kern, ctx.code_name, t);
        let cu = code_of(kern, ctx.code_name, u);
        let hyp = geq(kern, logic, nat_ty, ct, cu);
        let concl = geq(kern, logic, carrier, t, u);
        let with_h = arrow(kern, hyp, concl);
        pi_fv(kern, u_id, carrier, with_h)
    };

    let outer_motive = {
        let t_id = fv.next();
        let u_id = fv.next();
        let t = kernel.fvar(t_id);
        let body = claim(kernel, t, u_id);
        lam_fv(kernel, t_id, carrier, body)
    };

    let mut outer = vec![outer_motive];
    for oc in ctx.ctors {
        outer.push(outer_minor(kernel, c, ctx, oc, fv));
    }

    // --- the theorem ---------------------------------------------------------
    let t_id = fv.next();
    let u_id = fv.next();
    let h_id = fv.next();
    let t = kernel.fvar(t_id);
    let u = kernel.fvar(u_id);
    let h = kernel.fvar(h_id);
    let rec = kernel.const_(ctx.rec_name, vec![zero_lvl]);
    let induction = {
        let head = apply_all(kernel, rec, &outer);
        kernel.app(head, t)
    };
    let value_body = apply_all(kernel, induction, &[u, h]);

    let ct = code_of(kernel, ctx.code_name, t);
    let cu = code_of(kernel, ctx.code_name, u);
    let hyp_ty = geq(kernel, logic, nat_ty, ct, cu);
    let concl = geq(kernel, logic, carrier, t, u);
    let ty = {
        let with_h = arrow(kernel, hyp_ty, concl);
        pis(kernel, &[(t_id, carrier), (u_id, carrier)], with_h)
    };
    let value = {
        let with_h = lam_fv(kernel, h_id, hyp_ty, value_body);
        lams(kernel, &[(t_id, carrier), (u_id, carrier)], with_h)
    };
    let name = kernel.name_str(ctx.namespace, "code_injective");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// One outer minor premise: fix the left-hand constructor, then case-analyse
/// the right-hand one.
fn outer_minor(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    ctx: &InjCtx<'_>,
    oc: &Ctor,
    fv: &mut Fv,
) -> ExprId {
    let zero_lvl = kernel.level_zero();
    let logic = c.logic;
    let nat_ty = c.nat_ty;
    let carrier = ctx.carrier_ty;

    let field_ids: Vec<u64> = oc.fields.iter().map(|_| fv.next()).collect();
    let ih_ids: Vec<Option<u64>> = oc
        .fields
        .iter()
        .map(|k| {
            if *k == Field::Rec {
                Some(fv.next())
            } else {
                None
            }
        })
        .collect();

    let left_args: Vec<ExprId> = field_ids.iter().map(|id| kernel.fvar(*id)).collect();
    let p = {
        let head = kernel.const_(oc.name, vec![]);
        apply_all(kernel, head, &left_args)
    };

    // inner motive := fun u => Eq Nat (code p) (code u) -> Eq carrier p u
    let inner_claim = |kern: &mut crate::Kernel, u: ExprId| -> ExprId {
        let cp = code_of(kern, ctx.code_name, p);
        let cu = code_of(kern, ctx.code_name, u);
        let hyp = geq(kern, logic, nat_ty, cp, cu);
        let concl = geq(kern, logic, carrier, p, u);
        arrow(kern, hyp, concl)
    };
    let inner_motive = {
        let u_id = fv.next();
        let u = kernel.fvar(u_id);
        let body = inner_claim(kernel, u);
        lam_fv(kernel, u_id, carrier, body)
    };

    let mut inner = vec![inner_motive];
    for ic in ctx.ctors {
        inner.push(inner_minor(
            kernel,
            c,
            ctx,
            oc,
            ic,
            p,
            &left_args,
            &ih_ids,
            &inner_claim,
            fv,
        ));
    }

    let u_id = fv.next();
    let u = kernel.fvar(u_id);
    let rec = kernel.const_(ctx.rec_name, vec![zero_lvl]);
    let applied = {
        let head = apply_all(kernel, rec, &inner);
        kernel.app(head, u)
    };
    let body = lam_fv(kernel, u_id, carrier, applied);

    // Binders: the constructor's fields, then one induction hypothesis per
    // recursive field.
    let mut binders: Vec<(u64, ExprId)> = oc
        .fields
        .iter()
        .enumerate()
        .map(|(idx, kind)| {
            (
                field_ids[idx],
                field_ty(*kind, carrier, ctx.term_ty, nat_ty),
            )
        })
        .collect();
    for (idx, maybe) in ih_ids.iter().enumerate() {
        if let Some(id) = maybe {
            let arg = kernel.fvar(field_ids[idx]);
            let inner_u = fv.next();
            let ty = {
                let uu = kernel.fvar(inner_u);
                let carg = code_of(kernel, ctx.code_name, arg);
                let cuu = code_of(kernel, ctx.code_name, uu);
                let hyp = geq(kernel, logic, nat_ty, carg, cuu);
                let concl = geq(kernel, logic, carrier, arg, uu);
                let with_h = arrow(kernel, hyp, concl);
                pi_fv(kernel, inner_u, carrier, with_h)
            };
            binders.push((*id, ty));
        }
    }
    lams(kernel, &binders, body)
}

/// One inner minor premise: both constructors are now fixed.
fn inner_minor(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    ctx: &InjCtx<'_>,
    oc: &Ctor,
    ic: &Ctor,
    p: ExprId,
    left_args: &[ExprId],
    outer_ih_ids: &[Option<u64>],
    inner_claim: &dyn Fn(&mut crate::Kernel, ExprId) -> ExprId,
    fv: &mut Fv,
) -> ExprId {
    let logic = c.logic;
    let nat_ty = c.nat_ty;
    let carrier = ctx.carrier_ty;

    let field_ids: Vec<u64> = ic.fields.iter().map(|_| fv.next()).collect();
    let ih_ids: Vec<Option<u64>> = ic
        .fields
        .iter()
        .map(|k| {
            if *k == Field::Rec {
                Some(fv.next())
            } else {
                None
            }
        })
        .collect();
    let right_args: Vec<ExprId> = field_ids.iter().map(|id| kernel.fvar(*id)).collect();
    let q = {
        let head = kernel.const_(ic.name, vec![]);
        apply_all(kernel, head, &right_args)
    };

    let h_id = fv.next();
    let h = kernel.fvar(h_id);
    let cp = code_of(kernel, ctx.code_name, p);
    let cq = code_of(kernel, ctx.code_name, q);
    let hyp_ty = geq(kernel, logic, nat_ty, cp, cq);
    let goal = geq(kernel, logic, carrier, p, q);

    let body = if oc.tag == ic.tag {
        diagonal_case(
            kernel,
            c,
            ctx,
            oc,
            left_args,
            &right_args,
            outer_ih_ids,
            h,
            fv,
        )
    } else {
        off_diagonal_case(kernel, c, ctx, oc, ic, left_args, &right_args, h, goal, fv)
    };

    let with_h = lam_fv(kernel, h_id, hyp_ty, body);

    let mut binders: Vec<(u64, ExprId)> = ic
        .fields
        .iter()
        .enumerate()
        .map(|(idx, kind)| {
            (
                field_ids[idx],
                field_ty(*kind, carrier, ctx.term_ty, nat_ty),
            )
        })
        .collect();
    for (idx, maybe) in ih_ids.iter().enumerate() {
        if let Some(id) = maybe {
            let arg = kernel.fvar(field_ids[idx]);
            let ty = inner_claim(kernel, arg);
            binders.push((*id, ty));
        }
    }
    lams(kernel, &binders, with_h)
}

/// Different constructors: `pair_inj_left` reads the two tags off the
/// hypothesis and they are distinct numerals.
fn off_diagonal_case(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    ctx: &InjCtx<'_>,
    oc: &Ctor,
    ic: &Ctor,
    left_args: &[ExprId],
    right_args: &[ExprId],
    h: ExprId,
    goal: ExprId,
    fv: &mut Fv,
) -> ExprId {
    let logic = c.logic;
    let left_codes = component_codes(kernel, ctx, oc, left_args);
    let right_codes = component_codes(kernel, ctx, ic, right_args);
    let ltag = numeral(kernel, c, oc.tag);
    let rtag = numeral(kernel, c, ic.tag);
    let lpayload = payload(kernel, c, &left_codes);
    let rpayload = payload(kernel, c, &right_codes);
    let tags_eq = {
        let f = kernel.const_(c.pair_inj_left, vec![]);
        let applied = apply_all(kernel, f, &[ltag, lpayload, rtag, rpayload]);
        kernel.app(applied, h)
    };
    let contra = numeral_ne_absurd(kernel, c, logic, oc.tag, ic.tag, tags_eq, fv);
    false_elim(kernel, c, goal, contra)
}

/// The same constructor on both sides: peel the payload apart, convert each
/// component, and recombine by congruence.
fn diagonal_case(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    ctx: &InjCtx<'_>,
    oc: &Ctor,
    left_args: &[ExprId],
    right_args: &[ExprId],
    outer_ih_ids: &[Option<u64>],
    h: ExprId,
    fv: &mut Fv,
) -> ExprId {
    let logic = c.logic;
    let carrier = ctx.carrier_ty;

    if oc.fields.is_empty() {
        // `bot`: the two sides are the same closed term.
        let head = kernel.const_(oc.name, vec![]);
        return grefl(kernel, logic, carrier, head);
    }

    let left_codes = component_codes(kernel, ctx, oc, left_args);
    let right_codes = component_codes(kernel, ctx, oc, right_args);
    let ltag = numeral(kernel, c, oc.tag);
    let rtag = numeral(kernel, c, oc.tag);
    let lpayload = payload(kernel, c, &left_codes);
    let rpayload = payload(kernel, c, &right_codes);
    let payload_eq = {
        let f = kernel.const_(c.pair_inj_right, vec![]);
        let applied = apply_all(kernel, f, &[ltag, lpayload, rtag, rpayload]);
        kernel.app(applied, h)
    };
    let components = split_payload(
        kernel,
        c,
        c.pair_inj_left,
        c.pair_inj_right,
        &left_codes,
        &right_codes,
        payload_eq,
    );

    // Convert each component equality to one between the FIELDS.
    let mut proofs: Vec<Option<ExprId>> = Vec::new();
    let mut src_tys: Vec<ExprId> = Vec::new();
    for (idx, kind) in oc.fields.iter().enumerate() {
        let component = components[idx];
        match kind {
            Field::Nat => {
                proofs.push(Some(component));
                src_tys.push(c.nat_ty);
            }
            Field::Term => {
                let inj = ctx
                    .term_code_injective
                    .expect("a Term field needs FO.Term.code_injective");
                let f = kernel.const_(inj, vec![]);
                let applied = apply_all(kernel, f, &[left_args[idx], right_args[idx]]);
                let proof = kernel.app(applied, component);
                proofs.push(Some(proof));
                src_tys.push(ctx.term_ty);
            }
            Field::Rec => {
                let ih_id = outer_ih_ids[idx].expect("a recursive field has an outer IH");
                let ih = kernel.fvar(ih_id);
                let applied = kernel.app(ih, right_args[idx]);
                let proof = kernel.app(applied, component);
                proofs.push(Some(proof));
                src_tys.push(carrier);
            }
        }
    }

    let ctor_name = oc.name;
    let build = move |kern: &mut crate::Kernel, args: &[ExprId]| -> ExprId {
        let head = kern.const_(ctor_name, vec![]);
        apply_all(kern, head, args)
    };
    congr_args(
        kernel, logic, carrier, &src_tys, left_args, right_args, &proofs, &build, fv,
    )
}

/// The code of each field of `ctor` at the given argument list.
fn component_codes(
    kernel: &mut crate::Kernel,
    ctx: &InjCtx<'_>,
    ctor: &Ctor,
    args: &[ExprId],
) -> Vec<ExprId> {
    ctor.fields
        .iter()
        .enumerate()
        .map(|(idx, kind)| match kind {
            Field::Nat => args[idx],
            Field::Term => code_of(kernel, ctx.term_code, args[idx]),
            Field::Rec => code_of(kernel, ctx.code_name, args[idx]),
        })
        .collect()
}

#[cfg(test)]
mod tests;
