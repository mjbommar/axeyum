//! Alethe proof **emission** for datatype refutations decided via the
//! **read-over-construct simplification** (Track 3, phase P3.5 — ADR-0022 task
//! #21).
//!
//! [`prove_qf_dt_unsat_alethe_via_simplification`] closes the last trusted step
//! under a datatype `unsat` decided by [`axeyum_rewrite::simplify_datatypes`].
//! That reduction performs two denotation-preserving folds, bottom-up:
//!
//! - `select_i(construct_c(a0, …, an))` → `a_i` (the selector over the matching
//!   constructor is exactly that field); and
//! - `is_c(construct_d(…))` → `c == d` (the tester is the constant `c == d`).
//!
//! After folding, datatype operators built from explicit constructors vanish and
//! the residual is the underlying theory (bit-vectors / Booleans). The folds were,
//! until now, *trusted*: the residual refutation simply assumed them. They are
//! **datatype axioms**, not theorems of the residual theory.
//!
//! ## The composed proof and the trust boundary
//!
//! This emitter certifies the **`select`-over-`construct`** fold (the
//! read-over-construct fragment). For each redex `r = select_i(C(a…))`:
//!
//! 1. a fresh abstraction symbol `w` of `a_i`'s sort replaces `r` everywhere in
//!    the assertions, and the **projection equation** `(= w a_i)` is added to the
//!    residual. The bit-blast back-end ([`crate::prove_qf_bv_unsat_alethe_lowered`])
//!    refutes that residual, `assume`-ing each `(= w a_i)`;
//! 2. each such `assume` is spliced into a `!cong_*` derivation block:
//!
//!    ```text
//!    (assume !cong_defi_*  (= w (sel_c (C a…))))    ; abstraction definition (conservative)
//!    (assume !cong_proj_*  (= (sel_c (C a…)) a_i))  ; the DATATYPE PROJECTION AXIOM
//!    (step   !cong_trans_* (cl … (= w a_i)) :rule eq_transitive)
//!    (step   <assume_id>   (cl (= w a_i))   :rule resolution …)
//!    ```
//!
//!    The `!cong_*` namespace and the `!cong_trans_*`-referencing final step match
//!    the `QF_UFBV`/`QF_ABV` certificates, so the **shared**
//!    [`crate::reconstruct_qf_ufbv_proof`] reconstructs the result to a
//!    kernel-checked `False`.
//!
//! **The projection equation `(= (sel_c (C a…)) a_i)` is an assumed lemma.**
//! Unlike the Ackermann abstraction definition `(= v_i (f a))` (a conservative
//! fresh-variable introduction), this one is the datatype axiom itself — it is
//! *not* a theorem of pure EUF. `sel_c(C(a…)) = a_i` holds only because `sel_c` is
//! the recursor-defined `i`-th projection of `C`, which the EUF head does not
//! know. The reconstructor discharges it as a **kernel hypothesis axiom**
//! ([`crate::reconstruct_qf_ufbv_proof`] → `reconstruct_assume`), so the final
//! `False` is kernel-checked **relative to that projection lemma**. This is the
//! single trust point of the certificate (route B in the task taxonomy);
//! `check_alethe` has no datatype rule and Carcara has none either, so the
//! projection `assume` is internal-only — every *other* step (the abstraction
//! definition, the `eq_transitive`, the bit-blast tail) is Carcara-checkable.
//!
//! A future route-A certificate would model each datatype as a kernel inductive
//! and discharge the projection by ι-reduction (`Eq.refl`), removing this trust
//! point; the block shape here is chosen to make that swap local to the
//! reconstructor.
//!
//! Emission is **self-validating**: the assembled proof is run through
//! [`axeyum_cnf::check_alethe`] before return, so a returned certificate is always
//! checkable.

use std::collections::{HashMap, HashSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm, check_alethe};
use axeyum_ir::{ConstructorId, Op, Sort, SymbolId, TermArena, TermId, TermNode};

/// One `select`-over-`construct` projection fold whose result `a_i` the residual
/// refutation references through a fresh abstraction symbol `w`, with the data to
/// splice the projection-axiom derivation of `(= w a_i)`.
struct ProjectionCert {
    /// The fresh abstraction symbol standing for the redex (renders as `w`).
    fresh: SymbolId,
    /// The folded field result `a_i`.
    field: TermId,
    /// The constructor whose `index`-th projection is taken.
    constructor: ConstructorId,
    /// The selected field index.
    index: u32,
}

/// Emits a complete, checkable Alethe refutation for an `unsat` datatype
/// conjunction decided by read-over-construct simplification — with every
/// `select`-over-`construct` fold made explicit as an abstraction plus a
/// (kernel-discharged) **projection lemma** rather than silently folded — or
/// [`None`] when the query has no such fold, the residual `QF_BV` problem is
/// outside the bit-blast-emitter fragment, or the assembled proof fails
/// self-validation.
///
/// Requires `&mut TermArena` to intern the fresh abstraction symbols and the
/// projection / residual equalities.
///
/// The certificate reconstructs through [`crate::reconstruct_qf_ufbv_proof`] to a
/// kernel-checked `False`, **relative to** the per-fold projection lemma
/// `(= (sel_c (C a…)) a_i)` (module docs). The returned proof closes to `(cl)` and
/// has been accepted by [`axeyum_cnf::check_alethe`] before return.
///
/// Returns [`None`] when:
///
/// - no `select`-over-matching-`construct` redex occurs in the conjunction (a
///   pure-residual problem; use [`crate::prove_qf_bv_unsat_alethe`] directly);
/// - a folded field is not a bit-vector/Boolean residual term the bit-blast
///   emitter and the Alethe renderer handle; or
/// - the residual conjunction is outside the bit-blast emitter's fragment, is not
///   genuinely `unsat`, or the assembled proof fails its own
///   [`axeyum_cnf::check_alethe`] re-check.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_dt_unsat_alethe_via_simplification(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // 1. Collect every `select_i(construct_c(..))` redex (matching constructor) in
    //    the assertions, in a deterministic order. Each gets a fresh abstraction.
    let redexes = collect_projection_redexes(arena, assertions);
    if redexes.is_empty() {
        return None;
    }

    // Allocate a fresh abstraction symbol per distinct redex term.
    let mut subst: HashMap<TermId, TermId> = HashMap::new();
    let mut certs: Vec<ProjectionCert> = Vec::new();
    for (n, redex) in redexes.iter().enumerate() {
        let field_sort = arena.sort_of(redex.field);
        // Only residual (BV/Bool) field sorts are handled; a datatype-typed field
        // (nested datatype) would leave datatype content in the residual.
        if !matches!(field_sort, Sort::BitVec(_) | Sort::Bool) {
            return None;
        }
        let name = format!("!dt_w_{n}");
        let sym = arena.declare(&name, field_sort).ok()?;
        let w = arena.var(sym);
        subst.insert(redex.term, w);
        certs.push(ProjectionCert {
            fresh: sym,
            field: redex.field,
            constructor: redex.constructor,
            index: redex.index,
        });
    }

    // 2. Rewrite the assertions, replacing each redex with its abstraction `w`.
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut residual = Vec::with_capacity(assertions.len() + certs.len());
    for &assertion in assertions {
        residual.push(replace_subterms(arena, assertion, &subst, &mut memo).ok()?);
    }

    // 3. Add each projection equation `(= w a_i)` to the residual conjunction.
    for cert in &certs {
        let w = arena.var(cert.fresh);
        let eq = arena.eq(w, cert.field).ok()?;
        residual.push(eq);
    }

    // 4. Bit-blast refutation of the residual. It `assume`s each `(= w a_i)`.
    let bv_proof = crate::prove_qf_bv_unsat_alethe_lowered(arena, &residual)?;

    // 5. Splice: replace each projection `Assume` with its derivation block.
    let spliced = splice_projection_derivations(arena, &bv_proof, &certs)?;

    // 6. Self-validate before returning.
    if matches!(check_alethe(&spliced), Ok(true)) {
        Some(spliced)
    } else {
        None
    }
}

/// One `select_i(construct_c(..))` redex (the selector's constructor matching the
/// builder), with its folded field and the constructor application.
struct ProjectionRedex {
    /// The redex term `select_i(C(a…))`.
    term: TermId,
    /// The folded field result `a_i`.
    field: TermId,
    /// The constructor.
    constructor: ConstructorId,
    /// The field index `i`.
    index: u32,
}

/// Collects every distinct `select_i(construct_c(..))` redex whose selector
/// constructor matches the builder, in deterministic first-seen order.
fn collect_projection_redexes(arena: &TermArena, roots: &[TermId]) -> Vec<ProjectionRedex> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut out: Vec<ProjectionRedex> = Vec::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    // Walk in a stable order: process roots left-to-right, children left-to-right.
    stack.reverse();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::DtSelect { constructor, index } = op {
                let (constructor, index) = (*constructor, *index);
                if let Some((built, fields)) = as_construct(arena, args[0])
                    && built == constructor
                {
                    out.push(ProjectionRedex {
                        term,
                        field: fields[index as usize],
                        constructor,
                        index,
                    });
                }
            }
            // Push children (reversed so the leftmost is processed first).
            for &arg in args.iter().rev() {
                stack.push(arg);
            }
        }
    }
    out
}

/// If `term` is `construct_c(args…)`, returns `(c, args)`.
fn as_construct(arena: &TermArena, term: TermId) -> Option<(ConstructorId, Vec<TermId>)> {
    match arena.node(term) {
        TermNode::App {
            op: Op::DtConstruct { constructor, .. },
            args,
        } => Some((*constructor, args.to_vec())),
        _ => None,
    }
}

/// Rewrites `term`, replacing any subterm present in `subst` with its image,
/// rebuilding parents bottom-up. The replaced subterms are the projection redexes;
/// once replaced, no datatype operator remains above them in that branch.
fn replace_subterms(
    arena: &mut TermArena,
    term: TermId,
    subst: &HashMap<TermId, TermId>,
    memo: &mut HashMap<TermId, TermId>,
) -> Result<TermId, axeyum_ir::IrError> {
    if let Some(&w) = subst.get(&term) {
        return Ok(w);
    }
    if let Some(&cached) = memo.get(&term) {
        return Ok(cached);
    }
    let node = arena.node(term).clone();
    let result = match node {
        TermNode::App { op, args } => {
            let mut new_args = Vec::with_capacity(args.len());
            let mut changed = false;
            for &arg in &args {
                let na = replace_subterms(arena, arg, subst, memo)?;
                changed |= na != arg;
                new_args.push(na);
            }
            if changed {
                axeyum_rewrite::build_app(arena, op, &new_args)?
            } else {
                term
            }
        }
        _ => term,
    };
    memo.insert(term, result);
    Ok(result)
}

/// Replaces each projection `Assume { (= w a_i) }` in `bv_proof` with a `!cong_*`
/// derivation block deriving `(cl (= w a_i))` under the same id, so the fold is
/// made explicit (abstraction definition + projection axiom + `eq_transitive`).
fn splice_projection_derivations(
    arena: &TermArena,
    bv_proof: &[AletheCommand],
    certs: &[ProjectionCert],
) -> Option<Vec<AletheCommand>> {
    // Map each projection consequent's `(= w a_i)` clause key to its cert.
    let mut by_consequent: HashMap<String, &ProjectionCert> = HashMap::new();
    for cert in certs {
        let key = consequent_clause_key(arena, cert)?;
        by_consequent.insert(key, cert);
    }

    let mut out: Vec<AletheCommand> = Vec::with_capacity(bv_proof.len() + certs.len() * 4);
    let mut fresh = 0usize;
    for cmd in bv_proof {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                if let Some(cert) = projection_consequent_cert(clause, &by_consequent) {
                    emit_projection_derivation(arena, &mut out, &mut fresh, id, cert)?;
                } else {
                    out.push(cmd.clone());
                }
            }
            step @ AletheCommand::Step { .. } => out.push(step.clone()),
        }
    }
    Some(out)
}

/// If `clause` is a single positive literal `(= w a_i)` matching a registered
/// projection consequent, returns its cert.
fn projection_consequent_cert<'a>(
    clause: &[AletheLit],
    by_consequent: &HashMap<String, &'a ProjectionCert>,
) -> Option<&'a ProjectionCert> {
    let [lit] = clause else {
        return None;
    };
    if lit.negated {
        return None;
    }
    by_consequent.get(&lit.atom.key()).copied()
}

/// The `(= w a_i)` clause key for a projection consequent.
fn consequent_clause_key(arena: &TermArena, cert: &ProjectionCert) -> Option<String> {
    let w = sym_alethe(arena, cert.fresh);
    let field = term_to_alethe(arena, cert.field)?;
    Some(eq_term(w, field).key())
}

/// Emits, under `assume_id`, the steps deriving `(cl (= w a_i))` from the
/// abstraction definition `(= w (sel_c (C a…)))` and the projection axiom
/// `(= (sel_c (C a…)) a_i)`, chained by a single `eq_transitive`.
///
/// The projection axiom is the **assumed datatype lemma** (module docs); every
/// other step is Carcara-checkable.
fn emit_projection_derivation(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    cert: &ProjectionCert,
) -> Option<()> {
    let w = sym_alethe(arena, cert.fresh);
    let field = term_to_alethe(arena, cert.field)?;

    // `sel_c(C a…)` is rendered as a single **opaque constant** naming the redex
    // `select_index(C(a…))`. Its internal structure (the constructor and its
    // fields) is irrelevant to the head derivation — it is the shared middle term
    // of the transitive chain `w = sel = a_i`, so it cancels. An opaque const
    // keeps the EUF head reconstructor's term translation in scope (it models
    // `Const`/unary apps) and is Carcara-checkable as a plain symbol.
    let sel = AletheTerm::Const(selector_redex_name(arena, cert));

    // Abstraction definition `(= w (sel_c (C a…)))` — a conservative fresh-variable
    // introduction (the fresh `w` set equal to the selector application).
    let def_id = next_id(fresh, "defi");
    out.push(AletheCommand::Assume {
        id: def_id.clone(),
        clause: vec![pos(eq_term(w.clone(), sel.clone()))],
    });

    // Projection axiom `(= (sel_c (C a…)) a_i)` — the DATATYPE AXIOM (assumed
    // lemma; discharged by the reconstructor as a kernel hypothesis axiom).
    let proj_id = next_id(fresh, "proj");
    out.push(AletheCommand::Assume {
        id: proj_id.clone(),
        clause: vec![pos(eq_term(sel.clone(), field.clone()))],
    });

    // Chain w = sel_c(C a…) = a_i by a single `eq_transitive`.
    let trans = next_id(fresh, "trans");
    out.push(AletheCommand::Step {
        id: trans.clone(),
        clause: vec![
            neg(eq_term(w.clone(), sel.clone())),
            neg(eq_term(sel, field.clone())),
            pos(eq_term(w.clone(), field.clone())),
        ],
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });

    // Final resolution to (cl (= w a_i)), under the consequent's assume id, so
    // every downstream premise referencing the consequent resolves unchanged.
    out.push(AletheCommand::Step {
        id: assume_id.to_owned(),
        clause: vec![pos(eq_term(w, field))],
        rule: "resolution".to_owned(),
        premises: vec![trans, def_id, proj_id],
        args: Vec::new(),
    });

    Some(())
}

/// The synthetic opaque-constant name `!selapp_<ctor>_<index>_<redex>` standing
/// for the redex `select_index(C(a…))`. Keyed by the fresh abstraction symbol's
/// index so distinct redexes (distinct `w`) get distinct opaque names even when
/// they share a constructor and index.
fn selector_redex_name(arena: &TermArena, cert: &ProjectionCert) -> String {
    let name = arena.constructor_name(cert.constructor);
    format!("!selapp_{name}_{}_{}", cert.index, cert.fresh.index())
}

/// A fresh, namespaced derivation-step id (`!cong_<base>_<n>`), matching the
/// `QF_UFBV`/`QF_ABV` certificate namespace so the shared reconstructor
/// recognises the block.
fn next_id(fresh: &mut usize, base: &str) -> String {
    let id = format!("!cong_{base}_{}", *fresh);
    *fresh += 1;
    id
}

/// A symbol rendered as an Alethe `Const` of its declared name.
fn sym_alethe(arena: &TermArena, sym: SymbolId) -> AletheTerm {
    let (name, _sort) = arena.symbol(sym);
    AletheTerm::Const(name.to_owned())
}

/// Converts a folded field term to an [`AletheTerm`] for the residual fragment
/// (symbols and bit-vector/Boolean constants), or [`None`] otherwise. The fields
/// reaching here are residual (BV/Bool) by construction (the emitter declines
/// datatype-typed fields), so a non-leaf shape is out of scope.
fn term_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BoolConst(b) => Some(AletheTerm::Const(if *b { "true" } else { "false" }.into())),
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(bv_const_literal(*width, *value)))
        }
        _ => None,
    }
}

/// `(= a b)`.
fn eq_term(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("=".to_owned(), vec![a, b])
}

/// A positive literal.
fn pos(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: false,
    }
}

/// A negated literal.
fn neg(atom: AletheTerm) -> AletheLit {
    AletheLit {
        atom,
        negated: true,
    }
}

/// The SMT-LIB `#b…` literal for a bit-vector constant. Mirrors the renderer in
/// the other emitters so a rendered constant matches the rest of the stack.
fn bv_const_literal(width: u32, value: u128) -> String {
    let mut out = String::with_capacity(2 + width as usize);
    out.push_str("#b");
    for i in (0..width).rev() {
        let bit = (value >> i) & 1;
        out.push(if bit == 1 { '1' } else { '0' });
    }
    out
}
