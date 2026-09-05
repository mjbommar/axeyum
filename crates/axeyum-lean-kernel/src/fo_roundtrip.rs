//! **Slice 9 of the first-order model theory group** (`fo_*.rs`, ADR-1648):
//! the **decoder round trip** — the theorem `fo_decode.rs` was built to make
//! statable, and the one every representability argument was blocked on.
//!
//! ```text
//! FO.Term.size    : FO.Term    -> Nat
//! FO.Formula.size : FO.Formula -> Nat
//!
//! FO.Term.decode_code    : Π t f, Eq FO.Term
//!      (FO.Term.decodeAux (Nat.add f (FO.Term.size t)) (FO.Term.code t)) t
//! FO.Formula.decode_code : Π p f, Eq FO.Formula
//!      (FO.Formula.decodeAux (Nat.add f (FO.Formula.size p)) (FO.Formula.code p)) p
//!
//! FO.Term.decode_code_at_size    : Π t, Eq FO.Term
//!      (FO.Term.decodeAux (FO.Term.size t) (FO.Term.code t)) t
//! FO.Formula.decode_code_at_size : Π p, Eq FO.Formula
//!      (FO.Formula.decodeAux (FO.Formula.size p) (FO.Formula.code p)) p
//! ```
//!
//! ## The fuel goes on the LEFT of the `Nat.add`, and that is load-bearing
//!
//! `fo_decode.rs`'s module doc predicted this and it is exactly right. This
//! prelude's `Nat.add` recurses on its **right** argument, so `Nat.add f
//! (Nat.succ x)` ι-reduces to `Nat.succ (Nat.add f x)` while `Nat.add
//! (Nat.succ x) f` does not reduce at all. Every `size` below is a `Nat.succ`
//! at the head, so with the fuel on the left the goal
//!
//! ```text
//! decodeAux (Nat.add F (size (f1 k t))) (code (f1 k t))
//! ```
//!
//! ι-reduces — through `size`'s recursor, then `add`'s, then `decodeAux`'s —
//! to the decoder's step body at fuel `Nat.add F (size t)`, which is
//! **literally** the induction hypothesis's fuel at `f := F`. With the fuel on
//! the right (`Nat.add (size t) F`) nothing reduces and the minor premise does
//! not typecheck. The mutation is run in `fo_roundtrip/tests.rs`.
//!
//! ## One transport per tag, because `unpair` of a symbolic code is stuck
//!
//! `FO.Code.fst (FO.Code.pair 4 x)` is **not** definitionally `4`:
//! `FO.Code.fst` unfolds to `Nat.Pair.fst (FO.Code.unpair …)` and
//! `FO.Code.unpair` is a `Nat.rec` on the code, which is `FO.Code.pair 4 x` —
//! a `Nat.add` of a `FO.Code.tri`, not a numeral. So the decoder's nine-way
//! `Nat.rec` tag tree cannot ι-reduce on its own. Each of the thirteen minors
//! below therefore opens with a transport along `FO.Code.fst_pair`, after
//! which the scrutinee IS a literal numeral and the tree reduces to its arm;
//! the arm's payload projections are then rewritten one at a time along
//! `FO.Code.fst_pair`/`FO.Code.snd_pair`.
//!
//! The chain for a constructor with fields `v_1 … v_n` is always the same:
//!
//! ```text
//! decodeAux (add F (size (C v…))) (code (C v…))
//!   = tagCase (fst n) arms                     -- ι, definitional
//!   = arm_C (snd n)                            -- transport, FO.Code.fst_pair
//!   = arm_C P                                  -- congruence, FO.Code.snd_pair
//!   = C (g_1 c_1) … (g_n c_n)                  -- n or n+1 congruences on P
//!   = C v_1 … v_n                              -- one congruence per non-Nat field
//! ```
//!
//! where `g_i` is the identity on a `Nat` field, `FO.Term.decodeAux f` on a
//! `FO.Term` field of a `FO.Formula` constructor, and the recursor's own
//! induction hypothesis on a recursive field.
//!
//! ## `size` is a SUM, and the two binary cases pay for it with `add_assoc`
//!
//! `FO.Term.size (f2 k a b) = succ (add (size a) (size b))` — not a `max`,
//! deliberately: a `max` would drag `Nat.le` and its case analysis into every
//! minor, whereas a sum needs only `Nat.add_assoc` and `Nat.add_comm`. At
//! fuel `F` the binary case's inner fuel is `add F (add sa sb)`, and the two
//! induction hypotheses want it as `add (add F sb) sa` and `add (add F sa) sb`
//! respectively — one `gsymm (add_assoc …)` for the right child, and an
//! `add_comm` under `add F ·` before the same `gsymm` for the left one.
//!
//! ## What is NOT proved, and why it is not a gap that can be closed here
//!
//! `FO.Formula.decode (FO.Formula.code p) = p` — the SELF-fuelled wrapper —
//! does **not** follow. `FO.Formula.decode n := decodeAux n n`, so it would
//! need `Nat.le (size p) (code p)`, and that statement is **false**:
//! `FO.Formula.size FO.Formula.bot` is `1` while `FO.Formula.code
//! FO.Formula.bot` is `FO.Code.pair 0 0`, which is `Nat.zero`. The same
//! failure at `FO.Term.var 0`. Both are pinned by `def_eq` in this module's
//! tests, so the obstruction is a measurement and not an opinion.
//!
//! The self-fuelled wrappers are nevertheless *believed* correct, because the
//! decoder consumes one unit of fuel per constructor while `FO.Code.pair a b`
//! is strictly larger than `b`; the honest route is a strong induction on the
//! code with `Nat.lt (FO.Code.snd n) n`, which needs monotonicity of
//! `FO.Code.tri` and a well-founded `Nat` recursion this slice does not build.

// The mathematical variables in this group are the ones the literature uses --
// `t`/`u` for terms, `p`/`q` for formulas, `a`/`b`/`k`/`n` for naturals, `f`
// for fuel. Renaming them to satisfy `many_single_char_names` /
// `similar_names` would make every proof term harder to check against the
// arithmetic it encodes.
#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::fo_code::{CodeNames, nadd, nsucc, numeral, pair_app};
use crate::fo_syntax::{
    apply_all, arrow, gcongr, geq, geq_motive, grefl, gsymm, gtrans, gtransport, lam_fv, lams,
    pi_fv,
};
use crate::{
    BinderInfo, Declaration, ExprId, FoDecodePrelude, FoSyntaxPrelude, KernelError, LevelId,
    LogicPrelude, NameId, ReducibilityHint, build_fo_decode_prelude,
};

/// Names produced by [`build_fo_roundtrip_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoRoundTripPrelude {
    /// The decoder this inverts.
    pub decode: FoDecodePrelude,
    /// `FO.Term.size : FO.Term -> Nat`.
    pub term_size: NameId,
    /// `FO.Formula.size : FO.Formula -> Nat`.
    pub formula_size: NameId,
    /// `FO.Term.decode_code : Π t f, Eq FO.Term (decodeAux (add f (size t)) (code t)) t`.
    pub term_decode_code: NameId,
    /// `FO.Formula.decode_code : Π p f, Eq FO.Formula (decodeAux (add f (size p)) (code p)) p`.
    pub formula_decode_code: NameId,
    /// `FO.Term.decode_code_at_size : Π t, Eq FO.Term (decodeAux (size t) (code t)) t`.
    pub term_decode_code_at_size: NameId,
    /// `FO.Formula.decode_code_at_size : Π p, Eq FO.Formula (decodeAux (size p) (code p)) p`.
    pub formula_decode_code_at_size: NameId,
}

/// What one constructor field contributes to the code, to the size, and to the
/// round-trip chain.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Slot {
    /// A `Nat` field (a de Bruijn index or a symbol index): coded by itself,
    /// contributes nothing to the size, decoded by the identity.
    Nat,
    /// An `FO.Term` field of a `FO.Formula` constructor: coded by
    /// `FO.Term.code`, measured by `FO.Term.size`, decoded by
    /// `FO.Term.decodeAux` at the FORMULA decoder's own fuel.
    Term,
    /// A field of the type being recursed on.
    Rec,
}

/// One constructor of the inductive being inverted, in the numbering's tag
/// order (`fo_numbering.rs`).
struct Spec {
    ctor: NameId,
    tag: u32,
    slots: &'static [Slot],
}

/// The shared, immutable names.
struct Rt {
    c: CodeNames,
    dec: FoDecodePrelude,
    logic: LogicPrelude,
    nat_ty: ExprId,
    term_ty: ExprId,
    formula_ty: ExprId,
    zero_lvl: LevelId,
    one_lvl: LevelId,
}

/// A monotone supply of free-variable ids.
struct Fv(u64);

impl Fv {
    fn next(&mut self) -> u64 {
        self.0 += 1;
        self.0
    }
}

/// The per-carrier data the generic minor builder needs.
struct Family<'a> {
    specs: &'a [Spec],
    carrier: ExprId,
    decode_aux: NameId,
    code: NameId,
    size: NameId,
    rec_name: NameId,
    namespace: NameId,
    /// `FO.Term.size`, present only for the `FO.Formula` pass.
    term_size: Option<NameId>,
    /// `FO.Term.decode_code`, present only for the `FO.Formula` pass.
    term_decode_code: Option<NameId>,
}

/// Build the round-trip package.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_roundtrip_prelude(
    kernel: &mut crate::Kernel,
) -> Result<FoRoundTripPrelude, KernelError> {
    let dec = build_fo_decode_prelude(kernel)?;
    let syntax = dec.numbering.code.syntax;
    let c = CodeNames::rebuild(kernel, syntax.nat);
    let zero_lvl = kernel.level_zero();
    let one_lvl = kernel.level_succ(zero_lvl);
    let term_ty = kernel.const_(syntax.term, vec![]);
    let formula_ty = kernel.const_(syntax.formula, vec![]);
    let nat_ty = c.nat_ty;
    let rt = Rt {
        c,
        dec,
        logic: syntax.nat.logic,
        nat_ty,
        term_ty,
        formula_ty,
        zero_lvl,
        one_lvl,
    };
    let mut fv = Fv(1_648_000);

    let term_specs = term_specs(&syntax);
    let formula_specs = formula_specs(&syntax);

    let term_size = declare_term_size(kernel, &rt, &syntax, &mut fv)?;
    let formula_size = declare_formula_size(kernel, &rt, &syntax, term_size, &mut fv)?;

    let term_family = Family {
        specs: &term_specs,
        carrier: term_ty,
        decode_aux: dec.term_decode_aux,
        code: dec.numbering.term_code,
        size: term_size,
        rec_name: syntax.term_rec,
        namespace: syntax.term,
        term_size: None,
        term_decode_code: None,
    };
    let term_decode_code = declare_decode_code(kernel, &rt, &term_family, &mut fv)?;

    let formula_family = Family {
        specs: &formula_specs,
        carrier: formula_ty,
        decode_aux: dec.formula_decode_aux,
        code: dec.numbering.formula_code,
        size: formula_size,
        rec_name: syntax.formula_rec,
        namespace: syntax.formula,
        term_size: Some(term_size),
        term_decode_code: Some(term_decode_code),
    };
    let formula_decode_code = declare_decode_code(kernel, &rt, &formula_family, &mut fv)?;

    let term_decode_code_at_size =
        declare_at_size(kernel, &rt, &term_family, term_decode_code, &mut fv)?;
    let formula_decode_code_at_size =
        declare_at_size(kernel, &rt, &formula_family, formula_decode_code, &mut fv)?;

    Ok(FoRoundTripPrelude {
        decode: dec,
        term_size,
        formula_size,
        term_decode_code,
        formula_decode_code,
        term_decode_code_at_size,
        formula_decode_code_at_size,
    })
}

fn term_specs(syntax: &FoSyntaxPrelude) -> Vec<Spec> {
    vec![
        Spec {
            ctor: syntax.var,
            tag: 0,
            slots: &[Slot::Nat],
        },
        Spec {
            ctor: syntax.f0,
            tag: 1,
            slots: &[Slot::Nat],
        },
        Spec {
            ctor: syntax.f1,
            tag: 2,
            slots: &[Slot::Nat, Slot::Rec],
        },
        Spec {
            ctor: syntax.f2,
            tag: 3,
            slots: &[Slot::Nat, Slot::Rec, Slot::Rec],
        },
    ]
}

fn formula_specs(syntax: &FoSyntaxPrelude) -> Vec<Spec> {
    vec![
        Spec {
            ctor: syntax.bot,
            tag: 0,
            slots: &[],
        },
        Spec {
            ctor: syntax.eqf,
            tag: 1,
            slots: &[Slot::Term, Slot::Term],
        },
        Spec {
            ctor: syntax.rel1,
            tag: 2,
            slots: &[Slot::Nat, Slot::Term],
        },
        Spec {
            ctor: syntax.rel2,
            tag: 3,
            slots: &[Slot::Nat, Slot::Term, Slot::Term],
        },
        Spec {
            ctor: syntax.and_,
            tag: 4,
            slots: &[Slot::Rec, Slot::Rec],
        },
        Spec {
            ctor: syntax.or_,
            tag: 5,
            slots: &[Slot::Rec, Slot::Rec],
        },
        Spec {
            ctor: syntax.imp,
            tag: 6,
            slots: &[Slot::Rec, Slot::Rec],
        },
        Spec {
            ctor: syntax.all,
            tag: 7,
            slots: &[Slot::Rec],
        },
        Spec {
            ctor: syntax.ex,
            tag: 8,
            slots: &[Slot::Rec],
        },
    ]
}

// ============================================================================
// FO.Term.size and FO.Formula.size.
// ============================================================================

/// `FO.Term.size : FO.Term -> Nat` — one for a leaf, `succ` of the sum of the
/// children. See the module doc for why it is a sum and not a `max`.
fn declare_term_size(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    syntax: &FoSyntaxPrelude,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let carrier = rt.term_ty;
    let nat_ty = rt.nat_ty;
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, carrier, nat_ty, BinderInfo::Default)
    };
    let one = numeral(kernel, &rt.c, 1);

    // var / f0 : fun _ => 1
    let m_var = {
        let id = fv.next();
        lam_fv(kernel, id, nat_ty, one)
    };
    let m_f0 = {
        let id = fv.next();
        lam_fv(kernel, id, nat_ty, one)
    };

    // f1 : fun k t ih => succ ih
    let m_f1 = {
        let k_id = fv.next();
        let t_id = fv.next();
        let ih_id = fv.next();
        let ih = kernel.fvar(ih_id);
        let body = nsucc(kernel, &rt.c, ih);
        lams(
            kernel,
            &[(k_id, nat_ty), (t_id, carrier), (ih_id, nat_ty)],
            body,
        )
    };

    // f2 : fun k a b ia ib => succ (add ia ib)
    let m_f2 = {
        let k_id = fv.next();
        let a_id = fv.next();
        let b_id = fv.next();
        let ia_id = fv.next();
        let ib_id = fv.next();
        let ia = kernel.fvar(ia_id);
        let ib = kernel.fvar(ib_id);
        let sum = nadd(kernel, &rt.c, ia, ib);
        let body = nsucc(kernel, &rt.c, sum);
        lams(
            kernel,
            &[
                (k_id, nat_ty),
                (a_id, carrier),
                (b_id, carrier),
                (ia_id, nat_ty),
                (ib_id, nat_ty),
            ],
            body,
        )
    };

    let t_id = fv.next();
    let t = kernel.fvar(t_id);
    let rec = kernel.const_(syntax.term_rec, vec![rt.one_lvl]);
    let applied = apply_all(kernel, rec, &[motive, m_var, m_f0, m_f1, m_f2, t]);
    let value = lam_fv(kernel, t_id, carrier, applied);
    let ty = arrow(kernel, carrier, nat_ty);
    let name = kernel.name_str(syntax.term, "size");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Formula.size : FO.Formula -> Nat`. `FO.Term` fields are measured by
/// `FO.Term.size`, so the fuel a formula carries is enough for the terms it
/// contains — which is what the shared-fuel decoder of `fo_decode.rs` needs.
fn declare_formula_size(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    syntax: &FoSyntaxPrelude,
    term_size: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let carrier = rt.formula_ty;
    let term_ty = rt.term_ty;
    let nat_ty = rt.nat_ty;
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, carrier, nat_ty, BinderInfo::Default)
    };
    let one = numeral(kernel, &rt.c, 1);

    // bot : 1
    let m_bot = one;

    // eqf : fun t u => succ (add (Term.size t) (Term.size u))
    let m_eqf = {
        let t_id = fv.next();
        let u_id = fv.next();
        let t = kernel.fvar(t_id);
        let u = kernel.fvar(u_id);
        let st = size_app(kernel, term_size, t);
        let su = size_app(kernel, term_size, u);
        let sum = nadd(kernel, &rt.c, st, su);
        let body = nsucc(kernel, &rt.c, sum);
        lams(kernel, &[(t_id, term_ty), (u_id, term_ty)], body)
    };

    // rel1 : fun k t => succ (Term.size t)
    let m_rel1 = {
        let k_id = fv.next();
        let t_id = fv.next();
        let t = kernel.fvar(t_id);
        let st = size_app(kernel, term_size, t);
        let body = nsucc(kernel, &rt.c, st);
        lams(kernel, &[(k_id, nat_ty), (t_id, term_ty)], body)
    };

    // rel2 : fun k t u => succ (add (Term.size t) (Term.size u))
    let m_rel2 = {
        let k_id = fv.next();
        let t_id = fv.next();
        let u_id = fv.next();
        let t = kernel.fvar(t_id);
        let u = kernel.fvar(u_id);
        let st = size_app(kernel, term_size, t);
        let su = size_app(kernel, term_size, u);
        let sum = nadd(kernel, &rt.c, st, su);
        let body = nsucc(kernel, &rt.c, sum);
        lams(
            kernel,
            &[(k_id, nat_ty), (t_id, term_ty), (u_id, term_ty)],
            body,
        )
    };

    // and_ / or_ / imp : fun p q ip iq => succ (add ip iq)
    let mut binaries = Vec::new();
    for _ in 0..3 {
        let p_id = fv.next();
        let q_id = fv.next();
        let ip_id = fv.next();
        let iq_id = fv.next();
        let ip = kernel.fvar(ip_id);
        let iq = kernel.fvar(iq_id);
        let sum = nadd(kernel, &rt.c, ip, iq);
        let body = nsucc(kernel, &rt.c, sum);
        binaries.push(lams(
            kernel,
            &[
                (p_id, carrier),
                (q_id, carrier),
                (ip_id, nat_ty),
                (iq_id, nat_ty),
            ],
            body,
        ));
    }

    // all / ex : fun p ih => succ ih
    let mut quantifiers = Vec::new();
    for _ in 0..2 {
        let p_id = fv.next();
        let ih_id = fv.next();
        let ih = kernel.fvar(ih_id);
        let body = nsucc(kernel, &rt.c, ih);
        quantifiers.push(lams(kernel, &[(p_id, carrier), (ih_id, nat_ty)], body));
    }

    let p_id = fv.next();
    let p = kernel.fvar(p_id);
    let rec = kernel.const_(syntax.formula_rec, vec![rt.one_lvl]);
    let minors = [
        motive,
        m_bot,
        m_eqf,
        m_rel1,
        m_rel2,
        binaries[0],
        binaries[1],
        binaries[2],
        quantifiers[0],
        quantifiers[1],
        p,
    ];
    let applied = apply_all(kernel, rec, &minors);
    let value = lam_fv(kernel, p_id, carrier, applied);
    let ty = arrow(kernel, carrier, nat_ty);
    let name = kernel.name_str(syntax.formula, "size");
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
// Small combinators.
// ============================================================================

/// `<size> v`.
fn size_app(kernel: &mut crate::Kernel, size: NameId, v: ExprId) -> ExprId {
    let f = kernel.const_(size, vec![]);
    kernel.app(f, v)
}

/// `<code> v`.
fn code_app(kernel: &mut crate::Kernel, code: NameId, v: ExprId) -> ExprId {
    let f = kernel.const_(code, vec![]);
    kernel.app(f, v)
}

/// `FO.Code.fst n`.
fn fst_app(kernel: &mut crate::Kernel, rt: &Rt, n: ExprId) -> ExprId {
    let f = kernel.const_(rt.dec.numbering.code.fst, vec![]);
    kernel.app(f, n)
}

/// `FO.Code.snd n`.
fn snd_app(kernel: &mut crate::Kernel, rt: &Rt, n: ExprId) -> ExprId {
    let f = kernel.const_(rt.dec.numbering.code.snd, vec![]);
    kernel.app(f, n)
}

/// `FO.Code.fst_pair a b : Eq Nat (fst (pair a b)) a`.
fn fst_pair_pf(kernel: &mut crate::Kernel, rt: &Rt, a: ExprId, b: ExprId) -> ExprId {
    let f = kernel.const_(rt.dec.numbering.code.fst_pair, vec![]);
    apply_all(kernel, f, &[a, b])
}

/// `FO.Code.snd_pair a b : Eq Nat (snd (pair a b)) b`.
fn snd_pair_pf(kernel: &mut crate::Kernel, rt: &Rt, a: ExprId, b: ExprId) -> ExprId {
    let f = kernel.const_(rt.dec.numbering.code.snd_pair, vec![]);
    apply_all(kernel, f, &[a, b])
}

/// `<decodeAux> fuel code`.
fn decode_at(kernel: &mut crate::Kernel, aux: NameId, fuel: ExprId, code: ExprId) -> ExprId {
    let f = kernel.const_(aux, vec![]);
    apply_all(kernel, f, &[fuel, code])
}

/// `case scrutinee of 0 => arms[0] | … | _ => arms[last]`, the right-nested
/// `Nat.rec` chain at the CONSTANT motive `fun _ => result_ty` that
/// `fo_decode.rs`'s `tag_case` builds. Rebuilt here rather than imported
/// because the transport below needs the tree at a BOUND scrutinee, which is
/// the whole reason the tag transport exists; the fvar ids are derived from
/// the recursion depth so this is a pure function.
fn tag_case(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    result_ty: ExprId,
    scrutinee: ExprId,
    arms: &[ExprId],
    base: u64,
) -> ExprId {
    assert!(!arms.is_empty(), "a tag case tree needs a catch-all arm");
    if arms.len() == 1 {
        return arms[0];
    }
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, rt.nat_ty, result_ty, BinderInfo::Default)
    };
    let k_id = base;
    let ih_id = base + 1;
    let k = kernel.fvar(k_id);
    let rest = tag_case(kernel, rt, result_ty, k, &arms[1..], base + 2);
    let step = lams(kernel, &[(k_id, rt.nat_ty), (ih_id, result_ty)], rest);
    let rec = kernel.const_(rt.c.nat.rec, vec![rt.one_lvl]);
    apply_all(kernel, rec, &[motive, arms[0], step, scrutinee])
}

/// `payload [] = 0`, `[x] = x`, `[x, y] = pair x y`,
/// `[x, y, z] = pair x (pair y z)` — `fo_numbering.rs`'s `payload`.
fn code_payload(kernel: &mut crate::Kernel, rt: &Rt, codes: &[ExprId]) -> ExprId {
    match codes {
        [] => numeral(kernel, &rt.c, 0),
        [x] => *x,
        [x, rest @ ..] => {
            let tail = code_payload(kernel, rt, rest);
            pair_app(kernel, &rt.c, *x, tail)
        }
    }
}

/// The projections `fo_decode.rs`'s arms read a payload of the given arity
/// with: `[]`, `[p]`, `[fst p, snd p]`, `[fst p, fst (snd p), snd (snd p)]`.
fn payload_slots(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    arity: usize,
    payload: ExprId,
) -> Vec<ExprId> {
    match arity {
        0 => vec![],
        1 => vec![payload],
        2 => {
            let a = fst_app(kernel, rt, payload);
            let b = snd_app(kernel, rt, payload);
            vec![a, b]
        }
        _ => {
            let a = fst_app(kernel, rt, payload);
            let tail = snd_app(kernel, rt, payload);
            let b = fst_app(kernel, rt, tail);
            let c = snd_app(kernel, rt, tail);
            vec![a, b, c]
        }
    }
}

/// The decoder's argument for one slot: the identity on a `Nat` field,
/// `FO.Term.decodeAux f` on a `FO.Term` field, the carrier's own `decodeAux f`
/// on a recursive one.
fn slot_arg(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    fuel: ExprId,
    slot: Slot,
    x: ExprId,
) -> ExprId {
    match slot {
        Slot::Nat => x,
        Slot::Term => decode_at(kernel, rt.dec.term_decode_aux, fuel, x),
        Slot::Rec => decode_at(kernel, fam.decode_aux, fuel, x),
    }
}

/// `C (g_1 slots[0]) … (g_n slots[n-1])`.
fn arm_from_slots(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    spec: &Spec,
    fuel: ExprId,
    slots: &[ExprId],
) -> ExprId {
    let args: Vec<ExprId> = spec
        .slots
        .iter()
        .zip(slots)
        .map(|(slot, &x)| slot_arg(kernel, rt, fam, fuel, *slot, x))
        .collect();
    let head = kernel.const_(spec.ctor, vec![]);
    apply_all(kernel, head, &args)
}

/// The decoder arm for one constructor, as a function of the payload — exactly
/// the expression `fo_decode.rs` builds at `payload := FO.Code.snd n`.
fn arm_of_payload(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    spec: &Spec,
    fuel: ExprId,
    payload: ExprId,
) -> ExprId {
    let slots = payload_slots(kernel, rt, spec.slots.len(), payload);
    arm_from_slots(kernel, rt, fam, spec, fuel, &slots)
}

/// `C args…`.
fn apply_ctor(kernel: &mut crate::Kernel, spec: &Spec, args: &[ExprId]) -> ExprId {
    let head = kernel.const_(spec.ctor, vec![]);
    apply_all(kernel, head, args)
}

/// `Π (f : Nat), Eq C (decodeAux (Nat.add f (size v)) (code v)) v` — the
/// motive, and equally the induction hypothesis's type.
fn round_trip_at(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    v: ExprId,
    fv: &mut Fv,
) -> ExprId {
    let f_id = fv.next();
    let f = kernel.fvar(f_id);
    let s = size_app(kernel, fam.size, v);
    let fuel = nadd(kernel, &rt.c, f, s);
    let code = code_app(kernel, fam.code, v);
    let lhs = decode_at(kernel, fam.decode_aux, fuel, code);
    let body = geq(kernel, rt.logic, fam.carrier, lhs, v);
    pi_fv(kernel, f_id, rt.nat_ty, body)
}

// ============================================================================
// The round trip.
// ============================================================================

/// `<ns>.decode_code : Π t f, Eq <C> (decodeAux (Nat.add f (size t)) (code t)) t`.
fn declare_decode_code(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let carrier = fam.carrier;

    let motive = {
        let t_id = fv.next();
        let t = kernel.fvar(t_id);
        let body = round_trip_at(kernel, rt, fam, t, fv);
        lam_fv(kernel, t_id, carrier, body)
    };

    let mut minors = vec![motive];
    for spec in fam.specs {
        minors.push(minor_for(kernel, rt, fam, spec, fv));
    }

    let t_id = fv.next();
    let t = kernel.fvar(t_id);
    let rec = kernel.const_(fam.rec_name, vec![rt.zero_lvl]);
    let applied = {
        let head = apply_all(kernel, rec, &minors);
        kernel.app(head, t)
    };
    let value = lam_fv(kernel, t_id, carrier, applied);
    let ty = {
        let body = round_trip_at(kernel, rt, fam, t, fv);
        pi_fv(kernel, t_id, carrier, body)
    };
    let name = kernel.name_str(fam.namespace, "decode_code");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

/// One minor premise of the round trip: the chain described in the module doc.
fn minor_for(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    spec: &Spec,
    fv: &mut Fv,
) -> ExprId {
    let carrier = fam.carrier;
    let nat_ty = rt.nat_ty;
    let term_ty = rt.term_ty;
    let logic = rt.logic;

    // --- binders -------------------------------------------------------------
    let field_ids: Vec<u64> = spec.slots.iter().map(|_| fv.next()).collect();
    let ih_ids: Vec<Option<u64>> = spec
        .slots
        .iter()
        .map(|slot| {
            if *slot == Slot::Rec {
                Some(fv.next())
            } else {
                None
            }
        })
        .collect();
    let big_f_id = fv.next();
    let big_f = kernel.fvar(big_f_id);

    let values: Vec<ExprId> = field_ids.iter().map(|&id| kernel.fvar(id)).collect();

    let field_ty = |slot: Slot| match slot {
        Slot::Nat => nat_ty,
        Slot::Term => term_ty,
        Slot::Rec => carrier,
    };

    // The code of each field, and the size of each MEASURED field.
    let mut codes = Vec::with_capacity(spec.slots.len());
    let mut measured: Vec<(usize, ExprId)> = Vec::new();
    for (idx, slot) in spec.slots.iter().enumerate() {
        let v = values[idx];
        match slot {
            Slot::Nat => codes.push(v),
            Slot::Term => {
                let code = code_app(kernel, rt.dec.numbering.term_code, v);
                codes.push(code);
                let s = size_app(kernel, term_size_of(fam), v);
                measured.push((idx, s));
            }
            Slot::Rec => {
                let code = code_app(kernel, fam.code, v);
                codes.push(code);
                let s = size_app(kernel, fam.size, v);
                measured.push((idx, s));
            }
        }
    }

    // The decoder's inner fuel, in the shape the goal ι-reduces to.
    let fuel = match measured.len() {
        0 => big_f,
        1 => nadd(kernel, &rt.c, big_f, measured[0].1),
        _ => {
            let inner = nadd(kernel, &rt.c, measured[0].1, measured[1].1);
            nadd(kernel, &rt.c, big_f, inner)
        }
    };

    // --- the code of this constructor ---------------------------------------
    let tag_num = numeral(kernel, &rt.c, spec.tag);
    let payload = code_payload(kernel, rt, &codes);
    let n = pair_app(kernel, &rt.c, tag_num, payload);
    let snd_n = snd_app(kernel, rt, n);
    let fst_n = fst_app(kernel, rt, n);

    // --- step 1: the tag transport ------------------------------------------
    let arms: Vec<ExprId> = fam
        .specs
        .iter()
        .map(|s| arm_of_payload(kernel, rt, fam, s, fuel, snd_n))
        .collect();
    let arm_tag = arms[spec.tag as usize];

    let body_expr = tag_case(kernel, rt, carrier, fst_n, &arms, 1_649_000);

    let mut proof = {
        // `FO.Code.fst_pair`, turned around: `Eq Nat tag (FO.Code.fst n)`.
        let h = {
            let forward = fst_pair_pf(kernel, rt, tag_num, payload);
            let id = fv.next();
            gsymm(kernel, logic, nat_ty, fst_n, tag_num, forward, id)
        };
        let motive = {
            let id = fv.next();
            let arms_ref = &arms;
            geq_motive(
                kernel,
                logic,
                nat_ty,
                tag_num,
                &|k: &mut crate::Kernel, x: ExprId| {
                    let case = tag_case(k, rt, carrier, x, arms_ref, 1_649_100);
                    geq(k, logic, carrier, case, arm_tag)
                },
                id,
            )
        };
        let refl_case = grefl(kernel, logic, carrier, arm_tag);
        gtransport(kernel, logic, nat_ty, tag_num, motive, refl_case, fst_n, h)
    };
    let mut current = arm_tag;

    // --- step 2: the payload, then its projections --------------------------
    if !spec.slots.is_empty() {
        let h = snd_pair_pf(kernel, rt, tag_num, payload);
        let next = arm_of_payload(kernel, rt, fam, spec, fuel, payload);
        let step = {
            let id = fv.next();
            gcongr(
                kernel,
                logic,
                nat_ty,
                carrier,
                snd_n,
                payload,
                h,
                &|k: &mut crate::Kernel, y: ExprId| arm_of_payload(k, rt, fam, spec, fuel, y),
                id,
            )
        };
        let id = fv.next();
        proof = gtrans(
            kernel, logic, carrier, body_expr, current, next, proof, step, id,
        );
        current = next;
    }

    let mut slots = payload_slots(kernel, rt, spec.slots.len(), payload);

    if spec.slots.len() == 3 {
        // The payload is `pair c1 (pair c2 c3)`; rewriting the inner
        // `FO.Code.snd P` once fixes slots 1 and 2 together.
        let inner = pair_app(kernel, &rt.c, codes[1], codes[2]);
        let tail = snd_app(kernel, rt, payload);
        let h = snd_pair_pf(kernel, rt, codes[0], inner);
        let next_slots = {
            let b = fst_app(kernel, rt, inner);
            let c = snd_app(kernel, rt, inner);
            vec![slots[0], b, c]
        };
        let next = arm_from_slots(kernel, rt, fam, spec, fuel, &next_slots);
        let step = {
            let id = fv.next();
            let head = slots[0];
            gcongr(
                kernel,
                logic,
                nat_ty,
                carrier,
                tail,
                inner,
                h,
                &|k: &mut crate::Kernel, y: ExprId| {
                    let b = fst_app(k, rt, y);
                    let c = snd_app(k, rt, y);
                    arm_from_slots(k, rt, fam, spec, fuel, &[head, b, c])
                },
                id,
            )
        };
        let id = fv.next();
        proof = gtrans(
            kernel, logic, carrier, body_expr, current, next, proof, step, id,
        );
        current = next;
        slots = next_slots;
    }

    // Each remaining slot is `fst`/`snd` of a literal `FO.Code.pair`. A
    // one-field payload IS the field's code, so there is nothing to rewrite.
    if spec.slots.len() >= 2 {
        for idx in 0..spec.slots.len() {
            let h = slot_projection_proof(kernel, rt, spec, &codes, idx);
            let mut next_slots = slots.clone();
            next_slots[idx] = codes[idx];
            let next = arm_from_slots(kernel, rt, fam, spec, fuel, &next_slots);
            let step = {
                let id = fv.next();
                let base_slots = slots.clone();
                gcongr(
                    kernel,
                    logic,
                    nat_ty,
                    carrier,
                    slots[idx],
                    codes[idx],
                    h,
                    &|k: &mut crate::Kernel, x: ExprId| {
                        let mut s = base_slots.clone();
                        s[idx] = x;
                        arm_from_slots(k, rt, fam, spec, fuel, &s)
                    },
                    id,
                )
            };
            let id = fv.next();
            proof = gtrans(
                kernel, logic, carrier, body_expr, current, next, proof, step, id,
            );
            current = next;
            slots = next_slots;
        }
    }

    // --- step 3: the fields -------------------------------------------------
    let mut args: Vec<ExprId> = spec
        .slots
        .iter()
        .zip(&slots)
        .map(|(slot, &x)| slot_arg(kernel, rt, fam, fuel, *slot, x))
        .collect();

    for (position, &(idx, _)) in measured.clone().iter().enumerate() {
        let slot = spec.slots[idx];
        let hypothesis = field_proof(
            kernel,
            rt,
            fam,
            slot,
            values[idx],
            ih_ids[idx],
            big_f,
            &measured,
            position,
            fuel,
            fv,
        );
        let src = field_ty(slot);
        let mut next_args = args.clone();
        next_args[idx] = values[idx];
        let next = apply_ctor(kernel, spec, &next_args);
        let step = {
            let id = fv.next();
            let base_args = args.clone();
            gcongr(
                kernel,
                logic,
                src,
                carrier,
                args[idx],
                values[idx],
                hypothesis,
                &|k: &mut crate::Kernel, x: ExprId| {
                    let mut a = base_args.clone();
                    a[idx] = x;
                    apply_ctor(k, spec, &a)
                },
                id,
            )
        };
        let id = fv.next();
        proof = gtrans(
            kernel, logic, carrier, body_expr, current, next, proof, step, id,
        );
        current = next;
        args = next_args;
    }

    let expected = apply_ctor(kernel, spec, &values);
    assert_eq!(
        current, expected,
        "the rewrite chain must end at the constructor itself"
    );

    // --- abstract the binders -----------------------------------------------
    let with_fuel = lam_fv(kernel, big_f_id, nat_ty, proof);

    let mut binders: Vec<(u64, ExprId)> = spec
        .slots
        .iter()
        .enumerate()
        .map(|(idx, slot)| (field_ids[idx], field_ty(*slot)))
        .collect();
    for (idx, id) in ih_ids.clone().into_iter().enumerate() {
        if let Some(id) = id {
            let ih_ty = round_trip_at(kernel, rt, fam, values[idx], fv);
            binders.push((id, ih_ty));
        }
    }

    lams(kernel, &binders, with_fuel)
}

/// `FO.Term.size`, which a `FO.Formula` constructor's `FO.Term` fields are
/// measured by. Only ever asked for on the formula pass.
fn term_size_of(fam: &Family<'_>) -> NameId {
    fam.term_size
        .expect("a Term field only occurs on the FO.Formula pass")
}

/// `FO.Code.fst_pair`/`snd_pair` at the slot's own position in the payload.
fn slot_projection_proof(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    spec: &Spec,
    codes: &[ExprId],
    idx: usize,
) -> ExprId {
    match (spec.slots.len(), idx) {
        (2, 0) => fst_pair_pf(kernel, rt, codes[0], codes[1]),
        (2, 1) => snd_pair_pf(kernel, rt, codes[0], codes[1]),
        (3, 0) => {
            let inner = pair_app(kernel, &rt.c, codes[1], codes[2]);
            fst_pair_pf(kernel, rt, codes[0], inner)
        }
        (3, 1) => fst_pair_pf(kernel, rt, codes[1], codes[2]),
        (3, 2) => snd_pair_pf(kernel, rt, codes[1], codes[2]),
        _ => unreachable!("only arity 2 and 3 have stuck payload projections"),
    }
}

/// `Eq <field carrier> (decodeAux fuel (code v)) v` — the induction hypothesis
/// for a recursive field, `FO.Term.decode_code` for a `FO.Term` field, in both
/// cases preceded by the `Nat.add_assoc`/`Nat.add_comm` shuffle that turns the
/// decoder's inner fuel into the hypothesis's.
fn field_proof(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    slot: Slot,
    value: ExprId,
    ih_id: Option<u64>,
    big_f: ExprId,
    measured: &[(usize, ExprId)],
    position: usize,
    fuel: ExprId,
    fv: &mut Fv,
) -> ExprId {
    let logic = rt.logic;
    let nat_ty = rt.nat_ty;
    let (carrier, aux, code_name) = match slot {
        Slot::Term => (
            rt.term_ty,
            rt.dec.term_decode_aux,
            rt.dec.numbering.term_code,
        ),
        Slot::Rec => (fam.carrier, fam.decode_aux, fam.code),
        Slot::Nat => unreachable!("a Nat field needs no proof"),
    };

    // The fuel the hypothesis is instantiated at, and the equation that moves
    // the decoder's fuel to it.
    let (hypothesis_fuel, fuel_eq) = if measured.len() == 1 {
        (big_f, None)
    } else {
        let s_other = measured[1 - position].1;
        let s_mine = measured[position].1;
        let g = nadd(kernel, &rt.c, big_f, s_other);
        let target = nadd(kernel, &rt.c, g, s_mine);
        let assoc = {
            let f = kernel.const_(rt.c.nat.add_assoc, vec![]);
            apply_all(kernel, f, &[big_f, s_other, s_mine])
        };
        let inner_sum = nadd(kernel, &rt.c, s_other, s_mine);
        let via = nadd(kernel, &rt.c, big_f, inner_sum);
        let flipped = {
            let id = fv.next();
            gsymm(kernel, logic, nat_ty, target, via, assoc, id)
        };
        let h = if position == 1 {
            // `fuel` is already `add F (add s_other s_mine)`.
            flipped
        } else {
            // `fuel` is `add F (add s_mine s_other)`; commute first.
            let comm = {
                let f = kernel.const_(rt.c.nat.add_comm, vec![]);
                apply_all(kernel, f, &[s_mine, s_other])
            };
            let mine_first = nadd(kernel, &rt.c, s_mine, s_other);
            let step = {
                let id = fv.next();
                gcongr(
                    kernel,
                    logic,
                    nat_ty,
                    nat_ty,
                    mine_first,
                    inner_sum,
                    comm,
                    &|k: &mut crate::Kernel, x: ExprId| {
                        let f = k.const_(rt.c.nat.add, vec![]);
                        apply_all(k, f, &[big_f, x])
                    },
                    id,
                )
            };
            let id = fv.next();
            gtrans(kernel, logic, nat_ty, fuel, via, target, step, flipped, id)
        };
        (g, Some((h, target)))
    };

    let hypothesis = match slot {
        Slot::Rec => {
            let head = kernel.fvar(ih_id.expect("a recursive field has an induction hypothesis"));
            kernel.app(head, hypothesis_fuel)
        }
        Slot::Term => {
            let head = kernel.const_(
                fam.term_decode_code
                    .expect("a Term field only occurs on the FO.Formula pass"),
                vec![],
            );
            apply_all(kernel, head, &[value, hypothesis_fuel])
        }
        Slot::Nat => unreachable!("a Nat field needs no proof"),
    };

    let code = code_app(kernel, code_name, value);
    match fuel_eq {
        None => hypothesis,
        Some((h, target)) => {
            let lhs = decode_at(kernel, aux, fuel, code);
            let mid = decode_at(kernel, aux, target, code);
            let step = {
                let id = fv.next();
                gcongr(
                    kernel,
                    logic,
                    nat_ty,
                    carrier,
                    fuel,
                    target,
                    h,
                    &|k: &mut crate::Kernel, x: ExprId| decode_at(k, aux, x, code),
                    id,
                )
            };
            let id = fv.next();
            gtrans(
                kernel, logic, carrier, lhs, mid, value, step, hypothesis, id,
            )
        }
    }
}

/// `<ns>.decode_code_at_size : Π t, Eq C (decodeAux (size t) (code t)) t` —
/// `decode_code` at `f := Nat.zero`, moved across `Nat.zero_add`.
fn declare_at_size(
    kernel: &mut crate::Kernel,
    rt: &Rt,
    fam: &Family<'_>,
    decode_code: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let carrier = fam.carrier;
    let logic = rt.logic;
    let nat_ty = rt.nat_ty;

    let t_id = fv.next();
    let t = kernel.fvar(t_id);
    let zero = kernel.const_(rt.c.nat.zero, vec![]);
    let s = size_app(kernel, fam.size, t);
    let padded = nadd(kernel, &rt.c, zero, s);
    let code = code_app(kernel, fam.code, t);
    let lhs = decode_at(kernel, fam.decode_aux, padded, code);
    let rhs = decode_at(kernel, fam.decode_aux, s, code);

    let zero_add = {
        let f = kernel.const_(rt.c.nat.zero_add, vec![]);
        kernel.app(f, s)
    };
    let step = {
        let id = fv.next();
        gcongr(
            kernel,
            logic,
            nat_ty,
            carrier,
            padded,
            s,
            zero_add,
            &|k: &mut crate::Kernel, x: ExprId| decode_at(k, fam.decode_aux, x, code),
            id,
        )
    };
    let back = {
        let id = fv.next();
        gsymm(kernel, logic, carrier, lhs, rhs, step, id)
    };
    let at_zero = {
        let f = kernel.const_(decode_code, vec![]);
        apply_all(kernel, f, &[t, zero])
    };
    let body = {
        let id = fv.next();
        gtrans(kernel, logic, carrier, rhs, lhs, t, back, at_zero, id)
    };

    let concl = geq(kernel, logic, carrier, rhs, t);
    let ty = pi_fv(kernel, t_id, carrier, concl);
    let value = lam_fv(kernel, t_id, carrier, body);
    let name = kernel.name_str(fam.namespace, "decode_code_at_size");
    kernel.add_declaration(Declaration::Theorem {
        name,
        uparams: vec![],
        ty,
        value,
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests;
