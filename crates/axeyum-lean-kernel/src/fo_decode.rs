//! **Slice 8 of the first-order model theory group** (`fo_*.rs`, ADR-1640):
//! the **decoder** — the direction `fo_numbering.rs` does not have, and the
//! one every representability statement is blocked on.
//!
//! ```text
//! FO.Term.decodeAux    : Nat -> Nat -> FO.Term        -- (fuel, code)
//! FO.Term.decode       : Nat -> FO.Term       := fun n => decodeAux n n
//! FO.Formula.decodeAux : Nat -> Nat -> FO.Formula
//! FO.Formula.decode    : Nat -> FO.Formula    := fun n => decodeAux n n
//!
//! FO.Code.substCode     : Nat -> Nat -> Nat
//!   := fun cp ct => Formula.code (Formula.subst (Formula.decode cp)
//!                                  (Subst.cons (Term.decode ct) Subst.id))
//! FO.Code.isFormulaCode : Nat -> Bool
//!   := fun n => Nat.beq (Formula.code (Formula.decode n)) n
//! ```
//!
//! ## Why there is a fuel argument at all
//!
//! `FO.Code.unpair`'s recursion is structural on the code because the
//! anti-diagonal enumeration's step is a function of the previous *pair*
//! (`fo_code.rs`). A decoder's is not: it recurses on `FO.Code.snd n`, which
//! is smaller than `n` but not smaller by one constructor, so `Nat.rec` on the
//! code cannot express it. The prelude's standing device for exactly this is a
//! structural recursion on a separate **fuel** counter carrying the real
//! argument through as an ordinary parameter — `Nat.logAux`, `Nat.sqrtAux`,
//! `Nat.clogAux`, `Nat.minFacAux`, `Nat.testBitAux` and `Nat.binaryRecAux` are
//! all this shape — and that is what is used here. The motive of the outer
//! `Nat.rec` is `fun _ => Nat -> FO.Term` (resp. `-> FO.Formula`), so this is
//! large elimination, as those are.
//!
//! At zero fuel the decoders return a fixed default (`FO.Term.var 0`,
//! `FO.Formula.bot`). That is not a claim that the input was that term: it is
//! what makes the function TOTAL, which the kernel requires. Nothing here says
//! a decode is correct — see "what is deliberately absent" below.
//!
//! ## The tag dispatch is a nested `Nat.rec`, not a match
//!
//! Every code is `FO.Code.pair tag payload`, so decoding starts by reading the
//! tag and branching nine ways (four for `FO.Term`). This kernel has no
//! pattern match, so the branch is a right-nested chain of `Nat.rec`s at the
//! constant motive `fun _ => FO.Formula`: the `k`th `Nat.rec` splits "tag is
//! `k`" from "tag is at least `k+1`", and the last arm is the catch-all. That
//! makes the LAST constructor's tag the one a wrong tag falls into, which is
//! why `FO.Formula.ex` (tag 8) is last and why the module tests check a code
//! with an out-of-range tag lands there rather than assuming it cannot happen.
//!
//! ## `FO.Term`'s decoder takes the *formula* decoder's fuel
//!
//! `FO.Formula.eqf`, `rel1` and `rel2` carry `FO.Term` fields, and the formula
//! decoder decodes them with `FO.Term.decodeAux` at its OWN fuel rather than
//! at the term's self-fuelled `FO.Term.decode`. Self-fuelling there would make
//! the formula decoder's correctness depend on `size t <= code t` for terms as
//! well as on the formula bound, i.e. two bounds instead of one; passing the
//! fuel down keeps a single obligation for a later lane to discharge.
//!
//! ## What is deliberately absent, and why it is one thing
//!
//! **No round-trip theorem.** `FO.Formula.decode (FO.Formula.code p) = p` is
//! NOT proved here, and neither is the commuting lemma
//! `substCode (code p) (code t) = code (subst p (cons t id))` that would
//! follow from it in three `Eq` steps. This slice is the CONSTRUCTION half of
//! W3-7's second deliverable; the proof half needs three things, and the work
//! this slice did makes their cost precise rather than estimated:
//!
//! 1. **Size functions and a fuel-additive round trip.** State it as
//!    `Π t f, decodeAux (Nat.add f (size t)) (code t) = t` — with the fuel on
//!    the LEFT of the `add`, so `Nat.add f (Nat.succ x)` ι-reduces (this
//!    prelude's `Nat.add` recurses on its RIGHT argument) and the recursive
//!    call lands on exactly the induction hypothesis's fuel. The binary cases
//!    then need only `Nat.add_assoc` and `Nat.add_comm` to move `size a` and
//!    `size b` past each other — no `Nat.le`, no subtraction, no `max`.
//! 2. **A transport per tag.** `FO.Code.fst (code (and_ p q))` is not
//!    definitionally `4`: `FO.Code.fst` unfolds to `Nat.Pair.fst (unpair …)`
//!    and `unpair` of a symbolic code is stuck. So each of the nine minors
//!    must rewrite along `FO.Code.fst_pair`/`snd_pair` FIRST, after which the
//!    numeral is literal and the `Nat.rec` chain above ι-reduces. This is the
//!    part that was invisible before the decoder existed.
//! 3. **`size p <= code p`**, to justify `decode n := decodeAux n n`. Only
//!    needed for the self-fuelled wrappers; the `decodeAux` round trip in (1)
//!    does not use it.
//!
//! Recorded as the `open` fact `F:fo-formula-decoder`.

#![allow(clippy::many_single_char_names)]
#![allow(clippy::similar_names)]
#![allow(clippy::large_types_passed_by_value)]
#![allow(clippy::too_many_arguments)]
#![allow(clippy::too_many_lines)]

use crate::fo_code::{CodeNames, nzero};
use crate::fo_syntax::{apply_all, arrow, lam_fv, lams};
use crate::{
    BinderInfo, Declaration, ExprId, FoNumberingPrelude, KernelError, LevelId, NameId,
    ReducibilityHint, build_fo_numbering_prelude,
};

/// Names produced by [`build_fo_decode_prelude`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FoDecodePrelude {
    /// The numbering this inverts.
    pub numbering: FoNumberingPrelude,
    /// `FO.Term.decodeAux : Nat -> Nat -> FO.Term` (fuel, then code).
    pub term_decode_aux: NameId,
    /// `FO.Term.decode : Nat -> FO.Term := fun n => decodeAux n n`.
    pub term_decode: NameId,
    /// `FO.Formula.decodeAux : Nat -> Nat -> FO.Formula`.
    pub formula_decode_aux: NameId,
    /// `FO.Formula.decode : Nat -> FO.Formula := fun n => decodeAux n n`.
    pub formula_decode: NameId,
    /// `FO.Code.substCode : Nat -> Nat -> Nat`.
    pub subst_code: NameId,
    /// `FO.Code.isFormulaCode : Nat -> Bool`.
    pub is_formula_code: NameId,
}

/// A monotone supply of free-variable ids for the nested case trees.
struct Fv(u64);

impl Fv {
    fn next(&mut self) -> u64 {
        self.0 += 1;
        self.0
    }
}

/// Build the decoder package.
///
/// # Errors
///
/// Returns the [`KernelError`] from any of the underlying trusted gates if a
/// declaration fails to admit.
pub fn build_fo_decode_prelude(kernel: &mut crate::Kernel) -> Result<FoDecodePrelude, KernelError> {
    let numbering = build_fo_numbering_prelude(kernel)?;
    let c = CodeNames::rebuild(kernel, numbering.code.syntax.nat);
    let mut fv = Fv(1_645_000);

    let term_decode_aux = declare_term_decode_aux(kernel, &c, &numbering, &mut fv)?;
    let term_decode = declare_self_fuelled(
        kernel,
        &c,
        term_decode_aux,
        numbering.code.syntax.term,
        &mut fv,
    )?;
    let formula_decode_aux =
        declare_formula_decode_aux(kernel, &c, &numbering, term_decode_aux, &mut fv)?;
    let formula_decode = declare_self_fuelled(
        kernel,
        &c,
        formula_decode_aux,
        numbering.code.syntax.formula,
        &mut fv,
    )?;
    let subst_code =
        declare_subst_code(kernel, &c, &numbering, term_decode, formula_decode, &mut fv)?;
    let is_formula_code = declare_is_formula_code(kernel, &c, &numbering, formula_decode, &mut fv)?;

    Ok(FoDecodePrelude {
        numbering,
        term_decode_aux,
        term_decode,
        formula_decode_aux,
        formula_decode,
        subst_code,
        is_formula_code,
    })
}

// ============================================================================
// The tag case tree.
// ============================================================================

/// `case scrutinee of 0 => arms[0] | 1 => arms[1] | ... | _ => arms[last]`,
/// as a right-nested chain of `Nat.rec`s at the CONSTANT motive
/// `fun _ => result_ty`. The last arm is the catch-all, so it is what an
/// out-of-range tag decodes to.
fn tag_case(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    result_ty: ExprId,
    level: LevelId,
    scrutinee: ExprId,
    arms: &[ExprId],
    fv: &mut Fv,
) -> ExprId {
    assert!(!arms.is_empty(), "a tag case tree needs a catch-all arm");
    if arms.len() == 1 {
        return arms[0];
    }
    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, c.nat_ty, result_ty, BinderInfo::Default)
    };
    let k_id = fv.next();
    let ih_id = fv.next();
    let k = kernel.fvar(k_id);
    let rest = tag_case(kernel, c, result_ty, level, k, &arms[1..], fv);
    let step = lams(kernel, &[(k_id, c.nat_ty), (ih_id, result_ty)], rest);
    let rec = kernel.const_(c.nat.rec, vec![level]);
    apply_all(kernel, rec, &[motive, arms[0], step, scrutinee])
}

/// `FO.Code.fst n` / `FO.Code.snd n`.
fn code_fst(kernel: &mut crate::Kernel, p: &FoNumberingPrelude, n: ExprId) -> ExprId {
    let f = kernel.const_(p.code.fst, vec![]);
    kernel.app(f, n)
}

fn code_snd(kernel: &mut crate::Kernel, p: &FoNumberingPrelude, n: ExprId) -> ExprId {
    let f = kernel.const_(p.code.snd, vec![]);
    kernel.app(f, n)
}

// ============================================================================
// FO.Term.decodeAux.
// ============================================================================

/// `FO.Term.decodeAux : Nat -> Nat -> FO.Term`, structural on the FUEL.
///
/// ```text
/// decodeAux 0        n = FO.Term.var 0                     -- total, not correct
/// decodeAux (succ f) n =
///   case FO.Code.fst n of
///     0 => var (snd n)
///     1 => f0 (snd n)
///     2 => f1 (fst (snd n)) (decodeAux f (snd (snd n)))
///     _ => f2 (fst (snd n)) (decodeAux f (fst (snd (snd n))))
///                           (decodeAux f (snd (snd (snd n))))
/// ```
fn declare_term_decode_aux(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    p: &FoNumberingPrelude,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let syntax = p.code.syntax;
    let term_ty = kernel.const_(syntax.term, vec![]);
    let codomain = arrow(kernel, c.nat_ty, term_ty);

    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, c.nat_ty, codomain, BinderInfo::Default)
    };

    // At zero fuel: the constant `FO.Term.var 0`.
    let base = {
        let n_id = fv.next();
        let zero = nzero(kernel, c);
        let v = kernel.const_(syntax.var, vec![]);
        let body = kernel.app(v, zero);
        lam_fv(kernel, n_id, c.nat_ty, body)
    };

    let step = {
        let f_id = fv.next();
        let ih_id = fv.next();
        let n_id = fv.next();
        let ih = kernel.fvar(ih_id);
        let n = kernel.fvar(n_id);

        let tag = code_fst(kernel, p, n);
        let payload = code_snd(kernel, p, n);
        let payload_fst = code_fst(kernel, p, payload);
        let payload_snd = code_snd(kernel, p, payload);
        let payload_snd_fst = code_fst(kernel, p, payload_snd);
        let payload_snd_snd = code_snd(kernel, p, payload_snd);

        let arm_var = {
            let v = kernel.const_(syntax.var, vec![]);
            kernel.app(v, payload)
        };
        let arm_f0 = {
            let v = kernel.const_(syntax.f0, vec![]);
            kernel.app(v, payload)
        };
        let arm_f1 = {
            let sub = kernel.app(ih, payload_snd);
            let v = kernel.const_(syntax.f1, vec![]);
            apply_all(kernel, v, &[payload_fst, sub])
        };
        let arm_f2 = {
            let left = kernel.app(ih, payload_snd_fst);
            let right = kernel.app(ih, payload_snd_snd);
            let v = kernel.const_(syntax.f2, vec![]);
            apply_all(kernel, v, &[payload_fst, left, right])
        };

        let body = tag_case(
            kernel,
            c,
            term_ty,
            one,
            tag,
            &[arm_var, arm_f0, arm_f1, arm_f2],
            fv,
        );
        let with_n = lam_fv(kernel, n_id, c.nat_ty, body);
        lams(kernel, &[(f_id, c.nat_ty), (ih_id, codomain)], with_n)
    };

    let fuel_id = fv.next();
    let fuel = kernel.fvar(fuel_id);
    let rec = kernel.const_(c.nat.rec, vec![one]);
    let applied = apply_all(kernel, rec, &[motive, base, step, fuel]);
    let value = lam_fv(kernel, fuel_id, c.nat_ty, applied);
    let ty = arrow(kernel, c.nat_ty, codomain);
    let name = kernel.name_str(syntax.term, "decodeAux");
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
// FO.Formula.decodeAux.
// ============================================================================

/// `FO.Formula.decodeAux : Nat -> Nat -> FO.Formula`, structural on the fuel,
/// with a nine-way tag tree. `FO.Term` fields are decoded by
/// `FO.Term.decodeAux` at the SAME fuel (see the module doc).
fn declare_formula_decode_aux(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    p: &FoNumberingPrelude,
    term_decode_aux: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let one = {
        let zero = kernel.level_zero();
        kernel.level_succ(zero)
    };
    let syntax = p.code.syntax;
    let formula_ty = kernel.const_(syntax.formula, vec![]);
    let codomain = arrow(kernel, c.nat_ty, formula_ty);

    let motive = {
        let anon = kernel.anon();
        kernel.lam(anon, c.nat_ty, codomain, BinderInfo::Default)
    };

    let base = {
        let n_id = fv.next();
        let body = kernel.const_(syntax.bot, vec![]);
        lam_fv(kernel, n_id, c.nat_ty, body)
    };

    let step = {
        let f_id = fv.next();
        let ih_id = fv.next();
        let n_id = fv.next();
        let f = kernel.fvar(f_id);
        let ih = kernel.fvar(ih_id);
        let n = kernel.fvar(n_id);

        let tag = code_fst(kernel, p, n);
        let payload = code_snd(kernel, p, n);
        let payload_fst = code_fst(kernel, p, payload);
        let payload_snd = code_snd(kernel, p, payload);
        let payload_snd_fst = code_fst(kernel, p, payload_snd);
        let payload_snd_snd = code_snd(kernel, p, payload_snd);

        // `FO.Term.decodeAux f <code>` at the formula decoder's own fuel.
        let term_at = |kern: &mut crate::Kernel, code: ExprId| -> ExprId {
            let d = kern.const_(term_decode_aux, vec![]);
            apply_all(kern, d, &[f, code])
        };

        let arm_bot = kernel.const_(syntax.bot, vec![]);
        let arm_eqf = {
            let left = term_at(kernel, payload_fst);
            let right = term_at(kernel, payload_snd);
            let v = kernel.const_(syntax.eqf, vec![]);
            apply_all(kernel, v, &[left, right])
        };
        let arm_rel1 = {
            let arg = term_at(kernel, payload_snd);
            let v = kernel.const_(syntax.rel1, vec![]);
            apply_all(kernel, v, &[payload_fst, arg])
        };
        let arm_rel2 = {
            let left = term_at(kernel, payload_snd_fst);
            let right = term_at(kernel, payload_snd_snd);
            let v = kernel.const_(syntax.rel2, vec![]);
            apply_all(kernel, v, &[payload_fst, left, right])
        };
        let binary = |kern: &mut crate::Kernel, ctor: NameId| -> ExprId {
            let left = kern.app(ih, payload_fst);
            let right = kern.app(ih, payload_snd);
            let v = kern.const_(ctor, vec![]);
            apply_all(kern, v, &[left, right])
        };
        let arm_and = binary(kernel, syntax.and_);
        let arm_or = binary(kernel, syntax.or_);
        let arm_imp = binary(kernel, syntax.imp);
        let quantifier = |kern: &mut crate::Kernel, ctor: NameId| -> ExprId {
            let sub = kern.app(ih, payload);
            let v = kern.const_(ctor, vec![]);
            kern.app(v, sub)
        };
        let arm_all = quantifier(kernel, syntax.all);
        let arm_ex = quantifier(kernel, syntax.ex);

        let body = tag_case(
            kernel,
            c,
            formula_ty,
            one,
            tag,
            &[
                arm_bot, arm_eqf, arm_rel1, arm_rel2, arm_and, arm_or, arm_imp, arm_all, arm_ex,
            ],
            fv,
        );
        let with_n = lam_fv(kernel, n_id, c.nat_ty, body);
        lams(kernel, &[(f_id, c.nat_ty), (ih_id, codomain)], with_n)
    };

    let fuel_id = fv.next();
    let fuel = kernel.fvar(fuel_id);
    let rec = kernel.const_(c.nat.rec, vec![one]);
    let applied = apply_all(kernel, rec, &[motive, base, step, fuel]);
    let value = lam_fv(kernel, fuel_id, c.nat_ty, applied);
    let ty = arrow(kernel, c.nat_ty, codomain);
    let name = kernel.name_str(syntax.formula, "decodeAux");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `<namespace>.decode : Nat -> <carrier> := fun n => decodeAux n n` — the
/// code is its own fuel. Correct only once `size x <= code x` is proved; see
/// the module doc.
fn declare_self_fuelled(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    aux: NameId,
    namespace: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let n_id = fv.next();
    let n = kernel.fvar(n_id);
    let d = kernel.const_(aux, vec![]);
    let body = apply_all(kernel, d, &[n, n]);
    let value = lam_fv(kernel, n_id, c.nat_ty, body);
    let carrier = kernel.const_(namespace, vec![]);
    let ty = arrow(kernel, c.nat_ty, carrier);
    let name = kernel.name_str(namespace, "decode");
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
// The two arithmetic operations on codes.
// ============================================================================

/// `FO.Code.substCode : Nat -> Nat -> Nat` — substitution, as a function of
/// codes: decode the formula and the term, substitute the term for de Bruijn
/// index 0, and re-encode.
///
/// This is the shape a representability argument needs, and it is a
/// `Nat -> Nat -> Nat` exactly as the roadmap item asks. What it is NOT is a
/// proof: `substCode (code p) (code t) = code (subst p (Subst.cons t
/// Subst.id))` needs both decoders' round trips, and neither is proved.
fn declare_subst_code(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    p: &FoNumberingPrelude,
    term_decode: NameId,
    formula_decode: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let syntax = p.code.syntax;
    let cp_id = fv.next();
    let ct_id = fv.next();
    let cp = kernel.fvar(cp_id);
    let ct = kernel.fvar(ct_id);

    let formula = {
        let d = kernel.const_(formula_decode, vec![]);
        kernel.app(d, cp)
    };
    let term = {
        let d = kernel.const_(term_decode, vec![]);
        kernel.app(d, ct)
    };
    let substitution = {
        let cons = kernel.const_(syntax.subst_cons, vec![]);
        let id = kernel.const_(syntax.subst_id, vec![]);
        apply_all(kernel, cons, &[term, id])
    };
    let substituted = {
        let s = kernel.const_(syntax.formula_subst, vec![]);
        apply_all(kernel, s, &[formula, substitution])
    };
    let body = {
        let code = kernel.const_(p.formula_code, vec![]);
        kernel.app(code, substituted)
    };
    let value = lams(kernel, &[(cp_id, c.nat_ty), (ct_id, c.nat_ty)], body);
    let inner = arrow(kernel, c.nat_ty, c.nat_ty);
    let ty = arrow(kernel, c.nat_ty, inner);
    let name = kernel.name_str(c.code_ns, "substCode");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

/// `FO.Code.isFormulaCode : Nat -> Bool := fun n => Nat.beq (code (decode n)) n`
/// — decode and re-encode, and ask whether you got back what you started with.
///
/// Once `FO.Formula.code_injective` is joined by the round trip, this is a
/// decision procedure for "is a formula code", and `= Bool.true` on exactly
/// the image of `FO.Formula.code`. As it stands it is a computable `Nat ->
/// Bool` with an evaluation test and no theorem.
fn declare_is_formula_code(
    kernel: &mut crate::Kernel,
    c: &CodeNames,
    p: &FoNumberingPrelude,
    formula_decode: NameId,
    fv: &mut Fv,
) -> Result<NameId, KernelError> {
    let n_id = fv.next();
    let n = kernel.fvar(n_id);
    let decoded = {
        let d = kernel.const_(formula_decode, vec![]);
        kernel.app(d, n)
    };
    let recoded = {
        let code = kernel.const_(p.formula_code, vec![]);
        kernel.app(code, decoded)
    };
    let body = {
        let beq = kernel.const_(c.nat.beq, vec![]);
        apply_all(kernel, beq, &[recoded, n])
    };
    let value = lam_fv(kernel, n_id, c.nat_ty, body);
    let bool_ty = kernel.const_(c.logic.bool_, vec![]);
    let ty = arrow(kernel, c.nat_ty, bool_ty);
    let name = kernel.name_str(c.code_ns, "isFormulaCode");
    kernel.add_declaration(Declaration::Definition {
        name,
        uparams: vec![],
        ty,
        value,
        hint: ReducibilityHint::Regular(0),
    })?;
    Ok(name)
}

#[cfg(test)]
mod tests;
