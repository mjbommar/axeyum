//! Lexicographic-order (`str.<=` / `str.<`) refutation → kernel-checked Lean
//! `False` (P3.7 strings fragment).
//!
//! The in-tree lexicographic-order checker
//! ([`axeyum_strings::refute_lex`]) certifies a Boolean combination of
//! `str.<=` / `str.<` / word-equality atoms `unsat` behind an independent
//! re-derivation (ADR-0051; the lex order *is* the Unicode code-point order).
//! This module reconstructs one reachable class of that refutation over the
//! **free-monoid string prelude** ([`StringPrelude`], `Str = List Char`): it
//! builds a Lean proof term whose type is `False`, `infer`-checks it, and
//! `def_eq`-compares it to the prelude's `False`. A wrong reconstruction fails
//! that gate and is declined — never a wrong `False`.
//!
//! # What this slice covers — and what stays declined
//!
//! **Covered — the variable-independent false lex atom (the first-character
//! clash).** A `str.<=` / `str.<` atom that is **forced true** by the top-level
//! conjunction (a bare assertion, a conjunct, or a `¬∨` polarity fold) yet is
//! *variable-independently false* over its own operand words — i.e. at the first
//! position where both operands have a determined code point they differ with the
//! **left code greater** (`"AD"++x ≤ "AC"++y`), or the left is a proper
//! superstring of a fully-determined right (`"ab" ≤ "a"`), or a strict `<` holds
//! between two equal determined strings (`"ab" < "ab"`). The lexicographic
//! comparison ([`StringPrelude::lex_cmp_fn`]) ι-computes `lex L(s) L(t) ↝ false`
//! through the concrete determined prefix (opaque variable tails past the clash
//! are never forced), so the forced-true hypothesis `h : Eq Bool (lex L(s) L(t))
//! true` closes to `False` by the `Bool.true ≠ Bool.false` discriminator —
//! kernel-computed, no assumed order axiom.
//!
//! **Declined (documented follow-ups):** the **transitivity + first-character
//! clash** shape (Arm B: a multi-hop `s ≤* t` chain closed via word-equality
//! substitution) — needs lex-order transitivity, a genuine `List` induction; and
//! the **Boolean-skeleton constant fold** through `∨`/`⇒`/`xor`/`ite` beyond a
//! forced-true conjunct. Each is a safe decline to `unknown` (an `Err` from this
//! reconstructor), never a wrong verdict. The sole `unsat` gate remains
//! [`refute_lex`]; a target this slice cannot render is declined after that gate,
//! not misdecided.
#![allow(clippy::similar_names, clippy::many_single_char_names)]

use std::collections::{BTreeMap, BTreeSet};

use axeyum_lean_kernel::{
    BinderInfo, Declaration, ExprId, Kernel, NameId, StringPrelude, build_logic_prelude,
    build_string_prelude,
};
use axeyum_strings::{LexAtom, LexFormula, LexOutcome, LexProblem, Seg, refute_lex};

use crate::reconstruct::ReconstructError;

/// The rendered theorem name for a lexicographic-order refutation module. Matches
/// the shared `axeyum_refutation` audit name the real-Lean cross-check greps for in
/// `#print axioms` output.
const LEX_LEAN_THEOREM: &str = "axeyum_refutation";

/// Reconstruct a lexicographic-order refutation of `problem` to a self-contained,
/// kernel-checked Lean module, or a [`ReconstructError`] if this slice declines.
///
/// The refutation is first re-established by the independent [`refute_lex`] (the
/// sole `unsat` gate); the reconstruction then targets a forced-true,
/// variable-independently-false lex atom (see the module docs) and builds a
/// `False` proof gated by the kernel (`infer` + `def_eq False`).
///
/// # Errors
///
/// - [`ReconstructError::UnsupportedTerm`] — no certified lex refutation, or no
///   forced-true first-clash atom this slice renders (a transitivity/substitution
///   or Boolean-fold shape);
/// - [`ReconstructError::KernelRejected`] — the assembled proof did not `infer` to
///   `False` (an emitter bug, declined — never a wrong certificate).
pub fn reconstruct_lex_clash_to_lean_module(
    problem: &LexProblem,
) -> Result<String, ReconstructError> {
    // (1) The sole `unsat` gate: an independently re-checked refutation.
    if refute_lex(problem) != LexOutcome::Unsat {
        return Err(ReconstructError::UnsupportedTerm {
            term: "no independently-checked lexicographic refutation for this problem".to_owned(),
        });
    }

    // (2) Collect the atom indices the top-level conjunction forces TRUE.
    let mut forced: BTreeSet<usize> = BTreeSet::new();
    for f in &problem.assertions {
        collect_forced_true(f, true, &mut forced);
    }

    // (3) Pick a forced-true lex atom that is variable-independently FALSE over its
    // own words (a first-character clash), and reconstruct it.
    for &i in &forced {
        if let Some(LexAtom::Lex {
            left,
            right,
            strict,
        }) = problem.atoms.get(i)
            && eval_lex_const(left, right, *strict) == Some(false)
        {
            return build_clash_module(left, right, *strict);
        }
    }

    Err(ReconstructError::UnsupportedTerm {
        term: "lexicographic refutation is a transitivity/substitution or Boolean-fold shape \
               this slice defers"
            .to_owned(),
    })
}

// ---------------------------------------------------------------------------
// Certificate re-derivation (over the public LexProblem structure).
// ---------------------------------------------------------------------------

/// Collect the atom indices forced **true** by the top-level conjunction: a bare
/// atom, a conjunct of a top-level `and`, and (via `¬(a ∨ b) = ¬a ∧ ¬b`)
/// recursively through negations. Mirrors the in-checker forced-true collection.
fn collect_forced_true(f: &LexFormula, polarity: bool, out: &mut BTreeSet<usize>) {
    match f {
        LexFormula::Atom(i) if polarity => {
            out.insert(*i);
        }
        LexFormula::Not(g) => collect_forced_true(g, !polarity, out),
        LexFormula::And(gs) if polarity => {
            for g in gs {
                collect_forced_true(g, true, out);
            }
        }
        LexFormula::Or(gs) if !polarity => {
            for g in gs {
                collect_forced_true(g, false, out);
            }
        }
        _ => {}
    }
}

/// The variable-independent truth value of a lex atom `left (<|<=) right`, or
/// `None` when it depends on a variable tail. An independent re-derivation of the
/// in-checker `eval_lex_const`: it decides at the first position where both
/// operands have a determined code point that differ, or where one determined
/// operand ends against the other's determined continuation, or when two fully
/// determined operands coincide. A variable segment reached before any decision
/// yields `None`.
fn eval_lex_const(left: &[Seg], right: &[Seg], strict: bool) -> Option<bool> {
    let mut i = 0usize;
    loop {
        match (left.get(i), right.get(i)) {
            (None, None) => return Some(!strict),
            (None, Some(Seg::Lit(_))) => return Some(true),
            (Some(Seg::Lit(_)), None) => return Some(false),
            (Some(Seg::Lit(a)), Some(Seg::Lit(b))) => {
                if a != b {
                    return Some(a < b);
                }
            }
            (None | Some(_), None | Some(_)) => return None,
        }
        i += 1;
    }
}

// ---------------------------------------------------------------------------
// The reconstruction context: a kernel with the logic + string prelude.
// ---------------------------------------------------------------------------

/// A kernel seeded with the logical + string prelude, plus deterministic maps
/// from lex-order words/variables to their kernel encodings.
struct LexCtx {
    kernel: Kernel,
    sp: StringPrelude,
    /// Distinct code point → alphabet index (`Char.c<idx>`).
    char_index: BTreeMap<u32, usize>,
    /// Word variable name → opaque `Str` axiom name.
    seq_vars: BTreeMap<String, NameId>,
    next_id: u64,
}

impl LexCtx {
    /// A fresh context whose alphabet has one `Char` constructor per distinct code
    /// point in `codepoints` (deterministic, ascending order).
    fn new(codepoints: &BTreeSet<u32>) -> Self {
        let mut kernel = Kernel::new();
        let logic = build_logic_prelude(&mut kernel);
        let sp = build_string_prelude(&mut kernel, logic, codepoints.len());
        let char_index = codepoints
            .iter()
            .enumerate()
            .map(|(i, &c)| (c, i))
            .collect();
        Self {
            kernel,
            sp,
            char_index,
            seq_vars: BTreeMap::new(),
            next_id: 0,
        }
    }

    fn fresh_name(&mut self, base: &str) -> NameId {
        let anon = self.kernel.anon();
        let ns = self.kernel.name_str(anon, "axeyum.reconstruct.lex");
        let id = self.next_id;
        self.next_id += 1;
        let with_base = self.kernel.name_str(ns, base);
        self.kernel.name_num(with_base, id)
    }

    /// Declare a fresh axiom `_ : ty` and return its `Const` proof/term.
    fn axiom(&mut self, base: &str, ty: ExprId) -> Result<ExprId, ReconstructError> {
        let name = self.fresh_name(base);
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "lex".to_owned(),
                detail: format!("axiom {base} did not admit: {e:?}"),
            })?;
        Ok(self.kernel.const_(name, vec![]))
    }

    /// The opaque `Str` constant for a word variable (declared lazily).
    fn seq_var(&mut self, v: &str) -> Result<ExprId, ReconstructError> {
        if let Some(&name) = self.seq_vars.get(v) {
            return Ok(self.kernel.const_(name, vec![]));
        }
        let str_ty = self.sp.str_const(&mut self.kernel);
        let name = self.fresh_name("v");
        self.kernel
            .add_declaration(Declaration::Axiom {
                name,
                uparams: vec![],
                ty: str_ty,
            })
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "lex".to_owned(),
                detail: format!("word var axiom did not admit: {e:?}"),
            })?;
        self.seq_vars.insert(v.to_owned(), name);
        Ok(self.kernel.const_(name, vec![]))
    }

    /// Translate a lex-order word (a spine of determined code points and named
    /// variable spans) to its `Str` expression, right-to-left: a `Lit` prepends a
    /// concrete `cons`, a `Var` prepends the opaque `append` of that variable's
    /// `Str`. The determined leading prefix (through the deciding clash position)
    /// is therefore a flat `cons`-chain the comparison ι-reduces through.
    fn translate_word(&mut self, word: &[Seg]) -> Result<ExprId, ReconstructError> {
        let mut acc = self.sp.nil(&mut self.kernel);
        for seg in word.iter().rev() {
            acc = match seg {
                Seg::Lit(c) => {
                    let idx = *self.char_index.get(c).ok_or_else(|| {
                        ReconstructError::UnsupportedTerm {
                            term: format!("code point {c} missing from alphabet"),
                        }
                    })?;
                    let ch = self.sp.char(&mut self.kernel, idx);
                    self.sp.cons(&mut self.kernel, ch, acc)
                }
                Seg::Var(v) => {
                    let vs = self.seq_var(v)?;
                    self.sp.append_app(&mut self.kernel, vs, acc)
                }
            };
        }
        Ok(acc)
    }

    /// `Eq Bool x y`.
    fn mk_bool_eq(&mut self, x: ExprId, y: ExprId) -> ExprId {
        let z = self.kernel.level_zero();
        let one = self.kernel.level_succ(z);
        let bool_const = self.kernel.const_(self.sp.logic.bool_, vec![]);
        let eq = self.kernel.const_(self.sp.logic.eq, vec![one]);
        let e = self.kernel.app(eq, bool_const);
        let e = self.kernel.app(e, x);
        self.kernel.app(e, y)
    }

    /// Given `lhs : Bool` that ι-reduces to `Bool.false` and `h : Eq Bool lhs
    /// Bool.true`, build `False` via the `Bool.true ≠ Bool.false` discriminator.
    /// (The same closed construction the word-clash reconstruction uses.)
    fn bool_true_ne_false(&mut self, lhs: ExprId, h: ExprId) -> ExprId {
        let anon = self.kernel.anon();
        let bool_const = self.kernel.const_(self.sp.logic.bool_, vec![]);
        let prop = self.kernel.sort_zero();
        let true_const = self.kernel.const_(self.sp.logic.true_, vec![]);
        let false_const = self.kernel.const_(self.sp.logic.false_, vec![]);
        let z = self.kernel.level_zero();
        let one = self.kernel.level_succ(z);
        let rec = self.kernel.const_(self.sp.logic.bool_rec, vec![one]);
        let motive = self.kernel.lam(anon, bool_const, prop, BinderInfo::Default);
        let discr = {
            let e = self.kernel.app(rec, motive);
            let e = self.kernel.app(e, false_const); // minor for Bool.true
            let e = self.kernel.app(e, true_const); // minor for Bool.false
            let b = self.kernel.bvar(0);
            let body = self.kernel.app(e, b);
            self.kernel.lam(anon, bool_const, body, BinderInfo::Default)
        };
        let bool_true = self.kernel.const_(self.sp.logic.bool_true, vec![]);
        let transport_motive = {
            let x = self.kernel.bvar(1);
            let discr_x = self.kernel.app(discr, x);
            let eq = self.kernel.const_(self.sp.logic.eq, vec![one]);
            let x0 = self.kernel.bvar(0);
            let eq_lhs_x = {
                let e = self.kernel.app(eq, bool_const);
                let e = self.kernel.app(e, lhs);
                self.kernel.app(e, x0)
            };
            let inner = self
                .kernel
                .lam(anon, eq_lhs_x, discr_x, BinderInfo::Default);
            self.kernel
                .lam(anon, bool_const, inner, BinderInfo::Default)
        };
        let refl_case = self.kernel.const_(self.sp.logic.true_intro, vec![]);
        let rec_eq = self.kernel.const_(self.sp.logic.eq_rec, vec![z, one]);
        let e = self.kernel.app(rec_eq, bool_const);
        let e = self.kernel.app(e, lhs);
        let e = self.kernel.app(e, transport_motive);
        let e = self.kernel.app(e, refl_case);
        let e = self.kernel.app(e, bool_true);
        self.kernel.app(e, h)
    }

    /// Gate the assembled proof through the kernel (`infer` + `def_eq False`) and
    /// render the self-contained Lean module (with the `Char`/`Str`/`Bool`
    /// inductives so an external Lean regenerates their recursors *with* ι).
    fn gate_and_render(&mut self, proof: ExprId) -> Result<String, ReconstructError> {
        let inferred = self
            .kernel
            .infer(proof)
            .map_err(|e| ReconstructError::KernelRejected {
                rule: "lex".to_owned(),
                detail: format!("infer failed: {e:?}"),
            })?;
        let false_const = self.kernel.const_(self.sp.logic.false_, vec![]);
        if !self.kernel.def_eq(inferred, false_const) {
            return Err(ReconstructError::KernelRejected {
                rule: "lex".to_owned(),
                detail: "lexicographic refutation did not infer to False".to_owned(),
            });
        }
        let inductives = [self.sp.char_ind, self.sp.str_ind, self.sp.logic.bool_];
        let false_goal = self.kernel.const_(self.sp.logic.false_, vec![]);
        Ok(self.kernel.render_lean_module_with_inductives(
            LEX_LEAN_THEOREM,
            false_goal,
            proof,
            &inductives,
        ))
    }
}

/// Reconstruct a variable-independently-false forced-true lex atom `left ⋈ right`
/// (`⋈` is `<` when `strict`, else `≤`): the comparison `lex L(left) L(right)`
/// ι-reduces to `false`, so the forced-true hypothesis `h : Eq Bool (lex …) true`
/// closes to `False`.
fn build_clash_module(
    left: &[Seg],
    right: &[Seg],
    strict: bool,
) -> Result<String, ReconstructError> {
    let mut codepoints: BTreeSet<u32> = BTreeSet::new();
    for seg in left.iter().chain(right.iter()) {
        if let Seg::Lit(c) = seg {
            codepoints.insert(*c);
        }
    }
    let mut ctx = LexCtx::new(&codepoints);

    let le = ctx.translate_word(left)?;
    let re = ctx.translate_word(right)?;
    let cmp = ctx.sp.lex_cmp_fn(&mut ctx.kernel, strict);
    let lhs = {
        let e = ctx.kernel.app(cmp, le);
        ctx.kernel.app(e, re)
    };
    // h : Eq Bool (lex L(left) L(right)) true — the atom is forced true.
    let bool_true = ctx.kernel.const_(ctx.sp.logic.bool_true, vec![]);
    let h_ty = ctx.mk_bool_eq(lhs, bool_true);
    let h = ctx.axiom("h_atom", h_ty)?;
    let proof = ctx.bool_true_ne_false(lhs, h);
    ctx.gate_and_render(proof)
}

#[cfg(test)]
mod tests;
