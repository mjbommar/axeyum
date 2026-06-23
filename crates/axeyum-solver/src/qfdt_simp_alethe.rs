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
//! read-over-construct fragment) **and** the **is-tester** fold
//! (`is_C(K(args)) = true/false`, `K == C` iff `true`). The is-tester
//! certification is the read-over-construct twin: each `is_C(K(args))` redex is
//! abstracted to a fresh Boolean `w`, the **test-fold equation**
//! `(= (is_C (K args)) true/false)` is added as a (trusted) premise, and the
//! collapse `w = is_C(K args) = true/false` is closed by `eq_transitive` +
//! `resolution` — exactly the structural reasoning **Carcara checks** (it treats
//! the reserved tester/constructor heads as uninterpreted functions and the
//! test-fold as an asserted premise). The test fold itself stays a trusted
//! premise (like the projection equation); what is **certified** is its *use* in
//! the refutation. The field-unification datatype axioms (constructor
//! distinctness, injectivity, acyclicity) remain **trusted** and are out of scope
//! for this slice.
//!
//! Unlike the `select`-over-`construct` fold (whose route-A Lean reconstructor
//! ι-reduces the projection), the **Lean/kernel reconstruction route for the
//! is-tester collapse is deferred**: the fragment dispatch does not yet route a
//! datatype is-tester proof to a datatype reconstructor. The is-tester
//! certificate is therefore **Carcara-checked only** for now.
//!
//! For each redex `r = select_i(C(a…))`:
//!
//! 1. a fresh abstraction symbol `w` of `a_i`'s sort replaces `r` everywhere in
//!    the assertions, and the **projection equation** `(= w a_i)` is added to the
//!    residual. The bit-blast back-end ([`crate::prove_qf_bv_unsat_alethe_lowered`])
//!    refutes that residual, `assume`-ing each `(= w a_i)`;
//! 2. each such `assume` is spliced into a `!cong_*` derivation block:
//!
//!    ```text
//!    (assume !cong_defi_*  (= w (!dtsel_n_i_c (!dtcon_n_c a…))))   ; abstraction definition (conservative)
//!    (assume !cong_proj_*  (= (!dtsel_n_i_c (!dtcon_n_c a…)) a_i)) ; the projection equation (ι-reduction)
//!    (step   !cong_trans_* (cl … (= w a_i)) :rule eq_transitive)
//!    (step   <assume_id>   (cl (= w a_i))   :rule resolution …)
//!    ```
//!
//!    The `!cong_*` namespace and the `!cong_trans_*`-referencing final step match
//!    the `QF_UFBV`/`QF_ABV` certificates, so the **shared**
//!    [`crate::reconstruct_qf_ufbv_proof`] reconstructs the result to a
//!    kernel-checked `False`.
//!
//! ## Route A — the projection is **ι-reduction**, not an assumed axiom
//!
//! The selector application `sel_c(C a…)` is rendered **structurally** as a
//! reserved-named selector application `!dtsel_n_i_c` over a reserved-named
//! constructor application `!dtcon_n_c` (the heads carry the constructor arity
//! `n` and selected index `i`). The reconstructor's route-A datatype section
//! ([`crate::reconstruct_qf_ufbv_proof`] head path → `reconstruct_assume`)
//! recognises these heads, models the datatype `C` as a **kernel inductive** `D`
//! with one constructor `D.mk` of arity `n`, and models `select_i` as the
//! recursor application `λ t, D.rec (λ _ => α) (λ f… => f_i) t`. Then
//! `select_i(C a…)` ι-reduces (kernel `whnf`/`def_eq`) to `a_i`, so the
//! projection equation `(= (sel_c (C a…)) a_i)` is discharged by `Eq.refl` — it
//! is **derived, kernel-computed, not assumed**. The certificate carries **no
//! assumed datatype axiom**; its only axioms are the input assumptions (and `em`
//! from the bit-blast resolution layer), exactly like the other certificates.
//!
//! `check_alethe` and Carcara have no datatype rule, so for those checkers the
//! two reserved heads are plain uninterpreted functions and the projection
//! `assume` is an asserted premise (internal-only); every *other* step (the
//! abstraction definition, the `eq_transitive`, the bit-blast tail) is
//! Carcara-checkable. The kernel reconstruction is the checker that actually
//! discharges the projection by ι-reduction.
//!
//! Emission is **self-validating**: the assembled proof is run through
//! [`axeyum_cnf::check_alethe`] before return, so a returned certificate is always
//! checkable.

use std::collections::{HashMap, HashSet};

use axeyum_cnf::{AletheCommand, AletheLit, AletheTerm, check_alethe, check_alethe_with};
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
    /// The constructor's full field argument terms `a0 … a_{n-1}` (so the
    /// selector application `select_i(C a0…a_{n-1})` is rendered **structurally**
    /// for route-A reconstruction, where its projection ι-reduces).
    ctor_fields: Vec<TermId>,
}

/// One `is_c(construct_k(..))` is-tester fold whose Boolean result the residual
/// refutation references through a fresh `BitVec(1)` **truth-bit** abstraction
/// `w` (the redex is substituted by the predicate `(= w #b1)`), with the data to
/// splice the test-fold derivation of the truth-bit equation `(= w #b1/#b0)`.
struct TesterCert {
    /// The fresh `BitVec(1)` truth-bit abstraction symbol (renders `w`).
    fresh: SymbolId,
    /// The folded Boolean value (`tested == builder`): `#b1` when `true`.
    value: bool,
    /// The **tested** constructor `c` of `is_c(..)`.
    tested: ConstructorId,
    /// The **builder** constructor `k` of the argument `construct_k(..)`.
    builder: ConstructorId,
    /// The builder's full field argument terms (rendered for route-A structure).
    ctor_fields: Vec<TermId>,
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
/// kernel-checked `False` with **no assumed datatype axiom** — each per-fold
/// projection `(= (sel_c (C a…)) a_i)` is discharged by ι-reduction (`Eq.refl`)
/// over a kernel inductive (route A, module docs). The returned proof closes to
/// `(cl)` and has been accepted by [`axeyum_cnf::check_alethe`] before return.
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
    // 1. Collect every `select_i(construct_c(..))` redex (matching constructor) and
    //    every `is_c(construct_k(..))` is-tester redex in the assertions, in a
    //    deterministic order. Each gets a fresh abstraction.
    let redexes = collect_projection_redexes(arena, assertions);
    let tester_redexes = collect_tester_redexes(arena, assertions);
    if redexes.is_empty() && tester_redexes.is_empty() {
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
            ctor_fields: redex.ctor_fields.clone(),
        });
    }

    // Allocate, per distinct is-tester redex, a fresh **`BitVec(1)`** truth-bit
    // abstraction `w` and substitute the Bool redex `is_C(K a…)` with the Bool
    // **predicate** `(= w #b1)` — so the residual stays in the bit-blastable BV
    // fragment (a bare Bool atom is not a supported predicate). The truth bit is
    // `#b1` when `K == C`, `#b0` otherwise (the SMT-LIB tester semantics).
    let mut tester_certs: Vec<TesterCert> = Vec::new();
    for (n, redex) in tester_redexes.iter().enumerate() {
        let name = format!("!dt_t_{n}");
        let sym = arena.declare(&name, Sort::BitVec(1)).ok()?;
        let w = arena.var(sym);
        let one = arena.bv_const(1, 1).ok()?;
        let pred = arena.eq(w, one).ok()?;
        subst.insert(redex.term, pred);
        tester_certs.push(TesterCert {
            fresh: sym,
            value: redex.value,
            tested: redex.tested,
            builder: redex.builder,
            ctor_fields: redex.ctor_fields.clone(),
        });
    }

    // 2. Rewrite the assertions, replacing each redex with its abstraction `w`.
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let mut residual = Vec::with_capacity(assertions.len() + certs.len() + tester_certs.len());
    for &assertion in assertions {
        residual.push(replace_subterms(arena, assertion, &subst, &mut memo).ok()?);
    }

    // 3. Add each projection equation `(= w a_i)` to the residual conjunction.
    for cert in &certs {
        let w = arena.var(cert.fresh);
        let eq = arena.eq(w, cert.field).ok()?;
        residual.push(eq);
    }

    // 3b. Add each is-tester truth-fact to the residual as a unit over the SAME
    //     predicate atom `(= w #b1)` the occurrences use: `(= w #b1)` when the
    //     fold is `true`, `(not (= w #b1))` when `false`. This keeps the residual a
    //     bit-blast unit conflict (the BV emitter resolves opposite-polarity units
    //     of one atom), regardless of the tester's polarity in the assertion.
    for cert in &tester_certs {
        let w = arena.var(cert.fresh);
        let one = arena.bv_const(1, 1).ok()?;
        let pred = arena.eq(w, one).ok()?;
        let fact = if cert.value {
            pred
        } else {
            arena.not(pred).ok()?
        };
        residual.push(fact);
    }

    // 4. Bit-blast refutation of the residual. It `assume`s each `(= w a_i)` and
    //    each `(= w true/false)`.
    let bv_proof = crate::prove_qf_bv_unsat_alethe_lowered(arena, &residual)?;

    // 5. Splice: replace each projection / is-tester `Assume` with its block.
    let spliced = splice_projection_derivations(arena, &bv_proof, &certs, &tester_certs)?;

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
    /// The constructor's full field argument terms `a0 … a_{n-1}`.
    ctor_fields: Vec<TermId>,
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
                        ctor_fields: fields,
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

/// One `is_c(construct_k(..))` is-tester redex (any constructor pair), with its
/// folded Boolean value `c == k` and the builder's field arguments.
struct TesterRedex {
    /// The redex term `is_c(K(args…))`.
    term: TermId,
    /// The folded Boolean value (`tested == builder`).
    value: bool,
    /// The **tested** constructor `c`.
    tested: ConstructorId,
    /// The **builder** constructor `k`.
    builder: ConstructorId,
    /// The builder's full field argument terms `a0 … a_{n-1}`.
    ctor_fields: Vec<TermId>,
}

/// Collects every distinct `is_c(construct_k(..))` is-tester redex (any
/// constructor pair `c`, `k`) in deterministic first-seen order. The fold value
/// is `c == k`: `true` when the tested constructor is the builder, `false`
/// otherwise (the SMT-LIB tester semantics).
fn collect_tester_redexes(arena: &TermArena, roots: &[TermId]) -> Vec<TesterRedex> {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut out: Vec<TesterRedex> = Vec::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    stack.reverse();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermNode::App { op, args } = arena.node(term) {
            if let Op::DtTest(tested) = op {
                let tested = *tested;
                if let Some((builder, fields)) = as_construct(arena, args[0]) {
                    out.push(TesterRedex {
                        term,
                        value: builder == tested,
                        tested,
                        builder,
                        ctor_fields: fields,
                    });
                }
            }
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

/// Replaces each projection `Assume { (= w a_i) }` and each is-tester
/// `Assume { (= w true/false) }` in `bv_proof` with a `!cong_*` derivation block
/// deriving the same consequent under the same id, so the fold is made explicit
/// (abstraction definition + fold axiom + `eq_transitive`).
fn splice_projection_derivations(
    arena: &TermArena,
    bv_proof: &[AletheCommand],
    certs: &[ProjectionCert],
    tester_certs: &[TesterCert],
) -> Option<Vec<AletheCommand>> {
    // Map each projection consequent's `(= w a_i)` clause key to its cert.
    let mut by_consequent: HashMap<String, &ProjectionCert> = HashMap::new();
    for cert in certs {
        let key = consequent_clause_key(arena, cert)?;
        by_consequent.insert(key, cert);
    }
    // Map each is-tester consequent's `(= w true/false)` clause key to its cert.
    let mut by_tester: HashMap<String, &TesterCert> = HashMap::new();
    for cert in tester_certs {
        let key = tester_consequent_clause_key(arena, cert);
        by_tester.insert(key, cert);
    }

    let estimate = bv_proof.len() + (certs.len() + tester_certs.len()) * 4;
    let mut out: Vec<AletheCommand> = Vec::with_capacity(estimate);
    let mut fresh = 0usize;
    for cmd in bv_proof {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                if let Some(cert) = projection_consequent_cert(clause, &by_consequent) {
                    emit_projection_derivation(arena, &mut out, &mut fresh, id, cert)?;
                } else if let Some(cert) = tester_consequent_cert(clause, &by_tester) {
                    emit_tester_derivation(arena, &mut out, &mut fresh, id, cert)?;
                } else {
                    out.push(cmd.clone());
                }
            }
            step @ AletheCommand::Step { .. } => out.push(step.clone()),
        }
    }
    Some(out)
}

/// If `clause` is a single literal over the truth predicate `(= w #b1)` whose
/// polarity matches a registered is-tester consequent (positive for a `true`
/// fold, negated for `false`), returns its cert.
fn tester_consequent_cert<'a>(
    clause: &[AletheLit],
    by_tester: &HashMap<String, &'a TesterCert>,
) -> Option<&'a TesterCert> {
    let [lit] = clause else {
        return None;
    };
    let cert = by_tester.get(&lit.atom.key()).copied()?;
    // Positive literal ⇔ `true` fold; negated literal ⇔ `false` fold.
    (lit.negated != cert.value).then_some(cert)
}

/// The truth predicate atom `(= w #b1)` clause key for an is-tester consequent
/// (the polarity is carried by [`TesterCert::value`], not the key).
fn tester_consequent_clause_key(arena: &TermArena, cert: &TesterCert) -> String {
    let w = sym_alethe(arena, cert.fresh);
    eq_term(w, bit_alethe(true)).key()
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
/// abstraction definition `(= w (sel_c (C a…)))` and the projection equation
/// `(= (sel_c (C a…)) a_i)`, chained by a single `eq_transitive`.
///
/// `sel_c(C a…)` is rendered **structurally** as a reserved-named selector
/// application over a reserved-named constructor application
/// (`(!dtsel_n_i_c (!dtcon_n_c a0 … a_{n-1}))`) so the **route-A** reconstructor
/// recognises it, models the datatype as a kernel inductive, and discharges the
/// projection equation by **ι-reduction** (`Eq.refl`) — *not* an assumed axiom
/// (module docs). For Carcara (which has no datatype rule) the two reserved
/// heads are plain uninterpreted functions and the projection is an asserted
/// premise; every other step (the abstraction-definition resolution, the
/// `eq_transitive`, the bit-blast tail) is Carcara-checked structurally.
fn emit_projection_derivation(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    cert: &ProjectionCert,
) -> Option<()> {
    let w = sym_alethe(arena, cert.fresh);
    let field = term_to_alethe(arena, cert.field)?;

    // `sel_c(C a…)` rendered structurally: `(!dtsel_n_i_c (!dtcon_n_c a0 … an))`.
    // The reserved heads carry the constructor arity `n` and selected index `i`
    // so the route-A reconstructor can build the kernel inductive `D` (one ctor
    // `D.mk` of arity `n`) and the selector recursor application; the projection
    // then ι-reduces.
    let sel = selector_application_alethe(arena, cert)?;

    // Abstraction definition `(= w (sel_c (C a…)))` — a conservative fresh-variable
    // introduction (the fresh `w` set equal to the selector application).
    let def_id = next_id(fresh, "defi");
    out.push(AletheCommand::Assume {
        id: def_id.clone(),
        clause: vec![pos(eq_term(w.clone(), sel.clone()))],
    });

    // Projection equation `(= (sel_c (C a…)) a_i)` — DERIVED by ι-reduction in the
    // route-A reconstructor (the selector application is `def_eq` to `a_i`), so it
    // is `Eq.refl`, not an assumed datatype axiom.
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

/// The structural selector application `(!dtsel_n_i_c (!dtcon_n_c a0 … a_{n-1}))`
/// for the redex `select_i(C(a0…a_{n-1}))`, as an [`AletheTerm`].
///
/// The reserved heads name the constructor `c`, its arity `n`, and the selected
/// index `i`; the route-A reconstructor parses them ([`crate::reconstruct`]
/// `parse_dtcon`/`parse_dtsel`) to build the kernel inductive and prove the
/// projection by ι-reduction. Returns [`None`] if a field is not a renderable
/// residual leaf (the emitter already restricts fields to BV/Bool).
fn selector_application_alethe(arena: &TermArena, cert: &ProjectionCert) -> Option<AletheTerm> {
    let name = arena.constructor_name(cert.constructor);
    let n = cert.ctor_fields.len();
    // (!dtcon_n_c a0 … a_{n-1}).
    let mut con_args = Vec::with_capacity(n);
    for &f in &cert.ctor_fields {
        con_args.push(term_to_alethe(arena, f)?);
    }
    let con = AletheTerm::App(format!("!dtcon_{n}_{name}"), con_args);
    // (!dtsel_n_i_c <con>).
    Some(AletheTerm::App(
        format!("!dtsel_{n}_{}_{name}", cert.index),
        vec![con],
    ))
}

/// Emits, under `assume_id`, the steps deriving the is-tester **truth fact** over
/// the predicate `(= w #b1)` — `(cl (= w #b1))` when the fold is `true`, or
/// `(cl (not (= w #b1)))` when `false` — from the abstraction definition
/// `(= w (is_c (K a…)))` and the (trusted) test-fold premise.
///
/// `is_c(K a…)` is rendered **structurally** as a reserved-named tester
/// application over a reserved-named constructor application
/// (`(!dttest_n_c (!dtcon_m_K a0 … a_{m-1}))`): the tester head names the tested
/// constructor `c` and its field count `n`; the constructor head names the
/// builder `K` and its arity `m`. For Carcara (no datatype rule) both heads are
/// plain uninterpreted functions and the test-fold premise is an **asserted
/// premise** (the trusted is-tester fold); every *other* step (the
/// abstraction-definition resolution, the `eq_transitive` / `cong`+`equiv1`, the
/// bit-blast tail) is Carcara-checked structurally — the collapse reasoning is
/// what is certified. The Lean/kernel reconstruction route for the is-tester
/// collapse is deferred (the fragment dispatch does not yet route datatype
/// is-tester proofs to a datatype reconstructor), so this certificate is
/// Carcara-checked only.
fn emit_tester_derivation(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    cert: &TesterCert,
) -> Option<()> {
    let w = sym_alethe(arena, cert.fresh);
    let one = bit_alethe(true);
    // `is_c(K a…)` rendered structurally as the truth-bit tester application.
    let test = tester_application_alethe(arena, cert)?;

    // Abstraction definition `(= w (is_c (K a…)))` — fresh-variable introduction.
    let def_id = next_id(fresh, "defi");
    out.push(AletheCommand::Assume {
        id: def_id.clone(),
        clause: vec![pos(eq_term(w.clone(), test.clone()))],
    });

    if cert.value {
        emit_tester_true(out, fresh, assume_id, &def_id, &w, &test, &one);
    } else {
        emit_tester_false(out, fresh, assume_id, &def_id, &w, &test, &one);
    }
    Some(())
}

/// The `true` fold: derive `(= w #b1)` by `eq_transitive` over the abstraction
/// definition `(= w (is_c (K a…)))` and the trusted test-fold `(= (is_c (K a…)) #b1)`.
fn emit_tester_true(
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    def_id: &str,
    w: &AletheTerm,
    test: &AletheTerm,
    one: &AletheTerm,
) {
    // Test-fold premise `(= (is_c (K a…)) #b1)` — the TRUSTED is-tester fold.
    let fold_id = next_id(fresh, "test");
    out.push(AletheCommand::Assume {
        id: fold_id.clone(),
        clause: vec![pos(eq_term(test.clone(), one.clone()))],
    });
    // Chain w = is_c(K a…) = #b1 by a single `eq_transitive`.
    let trans = next_id(fresh, "trans");
    out.push(AletheCommand::Step {
        id: trans.clone(),
        clause: vec![
            neg(eq_term(w.clone(), test.clone())),
            neg(eq_term(test.clone(), one.clone())),
            pos(eq_term(w.clone(), one.clone())),
        ],
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    out.push(AletheCommand::Step {
        id: assume_id.to_owned(),
        clause: vec![pos(eq_term(w.clone(), one.clone()))],
        rule: "resolution".to_owned(),
        premises: vec![trans, def_id.to_owned(), fold_id],
        args: Vec::new(),
    });
}

/// The `false` fold: derive `(not (= w #b1))` from the abstraction definition
/// `(= w (is_c (K a…)))` and the trusted test-fold `(not (= (is_c (K a…)) #b1))`,
/// by `cong` (lifting `(= w T)` under the `=` head to
/// `(= (= w #b1) (= T #b1))`), `equiv1`, and `resolution`.
fn emit_tester_false(
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    def_id: &str,
    w: &AletheTerm,
    test: &AletheTerm,
    one: &AletheTerm,
) {
    let w_eq = eq_term(w.clone(), one.clone());
    let t_eq = eq_term(test.clone(), one.clone());
    // Test-fold premise `(not (= (is_c (K a…)) #b1))` — the TRUSTED is-tester fold.
    let fold_id = next_id(fresh, "test");
    out.push(AletheCommand::Assume {
        id: fold_id.clone(),
        clause: vec![neg(t_eq.clone())],
    });
    // cong: `(= (= w #b1) (= T #b1))` from `(= w T)` (the `#b1` arg is unchanged).
    let cong = next_id(fresh, "cong");
    out.push(AletheCommand::Step {
        id: cong.clone(),
        clause: vec![pos(eq_term(w_eq.clone(), t_eq.clone()))],
        rule: "cong".to_owned(),
        premises: vec![def_id.to_owned()],
        args: Vec::new(),
    });
    // equiv1: `(= A B)` ⇒ `(cl (not A) B)`, i.e. `(cl (not (= w #b1)) (= T #b1))`.
    let equiv = next_id(fresh, "equiv");
    out.push(AletheCommand::Step {
        id: equiv.clone(),
        clause: vec![neg(w_eq.clone()), pos(t_eq)],
        rule: "equiv1".to_owned(),
        premises: vec![cong],
        args: Vec::new(),
    });
    // resolution with the trusted `(not (= T #b1))` ⇒ `(not (= w #b1))`.
    out.push(AletheCommand::Step {
        id: assume_id.to_owned(),
        clause: vec![neg(w_eq)],
        rule: "resolution".to_owned(),
        premises: vec![equiv, fold_id],
        args: Vec::new(),
    });
}

/// The structural tester application `(!dttest_n_c (!dtcon_m_K a0 … a_{m-1}))`
/// for the redex `is_c(K(a0…a_{m-1}))`, as an [`AletheTerm`]. The tester head
/// names the tested constructor `c` and its field count `n`; the constructor
/// head names the builder `K` and its arity `m`. Returns [`None`] if a field is
/// not a renderable residual leaf (BV/Bool).
fn tester_application_alethe(arena: &TermArena, cert: &TesterCert) -> Option<AletheTerm> {
    let tested_name = arena.constructor_name(cert.tested);
    let tested_arity = arena.constructor_fields(cert.tested).len();
    let builder_name = arena.constructor_name(cert.builder);
    let m = cert.ctor_fields.len();
    // (!dtcon_m_K a0 … a_{m-1}).
    let mut con_args = Vec::with_capacity(m);
    for &f in &cert.ctor_fields {
        con_args.push(term_to_alethe(arena, f)?);
    }
    let con = AletheTerm::App(format!("!dtcon_{m}_{builder_name}"), con_args);
    // (!dttest_n_c <con>).
    Some(AletheTerm::App(
        format!("!dttest_{tested_arity}_{tested_name}"),
        vec![con],
    ))
}

/// The `BitVec(1)` truth-bit constant `#b1`/`#b0` as an [`AletheTerm`].
fn bit_alethe(value: bool) -> AletheTerm {
    AletheTerm::Const(if value { "#b1" } else { "#b0" }.into())
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

// =====================================================================
// Constructor DISTINCTNESS (gap-analysis Gap 14): `C(x…) = D(y…)` with
// distinct constructors `C != D` is refuted by COMPOSING the certified
// is-tester collapse with congruence — no new datatype axiom, no field
// unification.
// =====================================================================

/// Emits a complete, **Carcara-checkable** Alethe refutation of a single asserted
/// constructor equality `(= (C x…) (D y…))` whose two constructors are **distinct**
/// (`C != D`), or [`None`] when no such assertion is present or the assembled proof
/// fails self-validation.
///
/// # The composed proof (cong + is-tester folds + `#b1 != #b0`)
///
/// The refutation reuses the just-certified is-tester collapse and adds one
/// congruence lift; for the tested constructor `is_C`:
///
/// 1. `h` (the **trusted premise**): the asserted equality `(= (C x…) (D y…))`;
/// 2. `cong` lifts `h` under the tester head `is_C`:
///    `(= (is_C (C x…)) (is_C (D y…)))`;
/// 3. the two **is-tester folds** (the trusted folds the is-tester certificate
///    certifies the *use* of): `(= (is_C (C x…)) #b1)` (the true fold, `C == C`) and
///    `(= (is_C (D y…)) #b0)` (the false fold, `C != D`);
/// 4. a single `eq_transitive` chains `#b1 = is_C(C x…) = is_C(D y…) = #b0` to the
///    contradiction `(= #b1 #b0)`, discharged against the three equalities by
///    `resolution`;
/// 5. `evaluate` folds `(= (= #b1 #b0) false)` (distinct constants), `equiv1` +
///    the `false` tautology + `resolution` then close to the empty clause `(cl)`.
///
/// Every rule (`cong`, `eq_transitive`, `resolution`, `evaluate`, `equiv1`,
/// `false`) is exactly the set the is-tester certificate already uses, all
/// **Carcara-checkable**. The two reserved structural heads `!dttest_n_C` /
/// `!dtcon_m_K` are uninterpreted functions to Carcara (no datatype rule).
///
/// # Trust boundary (honest residual)
///
/// The constructor equality `(= (C x…) (D y…))` stays a **trusted premise** (`h`),
/// and the two is-tester folds stay trusted premises (as in the certified
/// is-tester collapse). What is **Carcara-certified** is the *distinctness
/// reasoning*: that a constructor equality between distinct `C != D` forces
/// `#b1 = #b0`, i.e. ⊥. Constructor **injectivity** (`C(x) = C(y) ⇒ x_i = y_i`)
/// and **acyclicity** remain **trusted/deferred** and are out of scope. The
/// Lean/kernel reconstruction route for the distinctness collapse is deferred too
/// (it composes the deferred is-tester reconstruction), so this certificate is
/// **Carcara-checked only**.
///
/// # Returns
///
/// [`None`] when no `(= (C x…) (D y…))` with distinct `C != D` and renderable
/// (BV/Bool) field leaves occurs in `assertions`, or when the assembled proof
/// fails its own narrow [`axeyum_cnf::check_alethe_with`] self-validation.
///
/// # Fragment boundary
///
/// Constructor fields are rendered as residual (`BitVec`/`Bool`) leaves; a
/// datatype-typed (nested) field returns [`None`]. The
/// constructor heads are rendered as **structural applications**
/// `(!dtcon_n_C args…)`, so a **nullary** constructor would render as the empty
/// application `(!dtcon_0_C)`, which the SMT-LIB front-end does not accept — only
/// constructors with at least one argument are in scope for this slice. Distinct
/// **same-constructor** equalities `(= (C x…) (C y…))` are declined (they need
/// injectivity, not distinctness).
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_dt_distinct_alethe_carcara(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Find the first asserted `(= (C x…) (D y…))` with distinct constructors.
    let (lhs_ctor, lhs_fields, rhs_ctor, rhs_fields) = assertions
        .iter()
        .find_map(|&assertion| match_distinct_constructor_eq(arena, assertion))?;

    // Render both constructor applications structurally (`!dtcon_n_C …`).
    let lhs_con = construct_alethe(arena, lhs_ctor, &lhs_fields)?;
    let rhs_con = construct_alethe(arena, rhs_ctor, &rhs_fields)?;

    // Tester `is_C` applied to each side: `(!dttest_n_C <con>)`.
    let test_lhs = tester_alethe(arena, lhs_ctor, lhs_con.clone());
    let test_rhs = tester_alethe(arena, lhs_ctor, rhs_con.clone());

    let one = bit_alethe(true);
    let zero = bit_alethe(false);
    let false_t = AletheTerm::Const("false".to_owned());

    // The contradictory bit equality `(= #b1 #b0)` and its `evaluate` fact.
    let bit_eq = eq_term(one.clone(), zero.clone());

    let proof = vec![
        // h: the TRUSTED constructor equality `(= (C x…) (D y…))`.
        AletheCommand::Assume {
            id: "h".to_owned(),
            clause: vec![pos(eq_term(lhs_con, rhs_con))],
        },
        // cong: lift `h` under the tester head: `(= (is_C (C x…)) (is_C (D y…)))`.
        dt_step(
            "cong",
            vec![pos(eq_term(test_lhs.clone(), test_rhs.clone()))],
            "cong",
            &["h"],
        ),
        // fold_true: the TRUSTED true is-tester fold `(= #b1 (is_C (C x…)))`.
        AletheCommand::Assume {
            id: "fold_true".to_owned(),
            clause: vec![pos(eq_term(one.clone(), test_lhs.clone()))],
        },
        // fold_false: the TRUSTED false is-tester fold `(= (is_C (D y…)) #b0)`.
        AletheCommand::Assume {
            id: "fold_false".to_owned(),
            clause: vec![pos(eq_term(test_rhs.clone(), zero.clone()))],
        },
        // chain: `eq_transitive` over `#b1 = is_C(C x…) = is_C(D y…) = #b0`.
        dt_step(
            "chain",
            vec![
                neg(eq_term(one.clone(), test_lhs.clone())),
                neg(eq_term(test_lhs, test_rhs.clone())),
                neg(eq_term(test_rhs, zero)),
                pos(bit_eq.clone()),
            ],
            "eq_transitive",
            &[],
        ),
        // contra: resolve the chain against the three equalities ⇒ `(= #b1 #b0)`.
        dt_step(
            "contra",
            vec![pos(bit_eq.clone())],
            "resolution",
            &["chain", "fold_true", "cong", "fold_false"],
        ),
        // ev: `evaluate` folds the distinct-constant equality to `false`.
        dt_step(
            "ev",
            vec![pos(eq_term(bit_eq.clone(), false_t.clone()))],
            "evaluate",
            &[],
        ),
        // e1: `equiv1` over `ev` ⇒ `(cl (not (= #b1 #b0)) false)`.
        dt_step(
            "e1",
            vec![neg(bit_eq.clone()), pos(false_t.clone())],
            "equiv1",
            &["ev"],
        ),
        // ff: the `false` tautology ⇒ `(cl (not false))`.
        dt_step("ff", vec![neg(false_t)], "false", &[]),
        // empty: resolve `(= #b1 #b0)`, `(cl (not (= #b1 #b0)) false)`, `(cl (not
        // false))` to the empty clause.
        dt_step("empty", Vec::new(), "resolution", &["contra", "e1", "ff"]),
    ];

    // Self-validate with the narrow distinctness hook (Carcara is the trust anchor).
    matches!(check_alethe_with(&proof, &distinct_simplify_hook), Ok(true)).then_some(proof)
}

/// If `assertion` is `(= (C x…) (D y…))` with both sides constructor applications
/// and **distinct** constructors `C != D`, returns `(C, x…, D, y…)`; else [`None`].
///
/// The two constructors must also share the same datatype sort (the SMT-LIB
/// equality is sort-homogeneous), which is guaranteed by the arena's well-typed
/// `eq` builder.
fn match_distinct_constructor_eq(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(ConstructorId, Vec<TermId>, ConstructorId, Vec<TermId>)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(assertion) else {
        return None;
    };
    let &[x, y] = &args[..] else {
        return None;
    };
    let (lhs_ctor, lhs_fields) = as_construct(arena, x)?;
    let (rhs_ctor, rhs_fields) = as_construct(arena, y)?;
    (lhs_ctor != rhs_ctor).then_some((lhs_ctor, lhs_fields, rhs_ctor, rhs_fields))
}

/// The structural constructor application `(!dtcon_n_C a0 … a_{n-1})` for
/// `C(a0…a_{n-1})`, as an [`AletheTerm`]. Returns [`None`] if a field is not a
/// renderable residual leaf (BV/Bool symbol or constant).
fn construct_alethe(
    arena: &TermArena,
    ctor: ConstructorId,
    fields: &[TermId],
) -> Option<AletheTerm> {
    let name = arena.constructor_name(ctor);
    let n = fields.len();
    let mut con_args = Vec::with_capacity(n);
    for &f in fields {
        con_args.push(term_to_alethe(arena, f)?);
    }
    Some(AletheTerm::App(format!("!dtcon_{n}_{name}"), con_args))
}

/// The structural tester application `(!dttest_n_C <con>)` applying the tester for
/// constructor `tested` (field count `n`) to the already-rendered constructor
/// term `con`.
fn tester_alethe(arena: &TermArena, tested: ConstructorId, con: AletheTerm) -> AletheTerm {
    let name = arena.constructor_name(tested);
    let arity = arena.constructor_fields(tested).len();
    AletheTerm::App(format!("!dttest_{arity}_{name}"), vec![con])
}

/// The narrow self-validation hook for [`prove_qf_dt_distinct_alethe_carcara`]:
/// accepts `evaluate` only for the exact unit `(= (= #b1 #b0) false)` (the bit
/// equality folding to `false`) and `false` only for the unit `(cl (not false))`.
/// Every other rule defers (`None`) to the native checker (`cong`, `eq_transitive`,
/// `equiv1`, `resolution` are all natively handled). These are precisely the two
/// shapes the emitter produces that the native checker does not handle, and exactly
/// the simplifications Carcara independently checks.
fn distinct_simplify_hook(rule: &str, clause: &[AletheLit]) -> Option<bool> {
    match rule {
        // `(= (= #b1 #b0) false)` — the distinct-constant bit equality folds to
        // `false`.
        "evaluate" => {
            let [lit] = clause else {
                return Some(false);
            };
            if lit.negated {
                return Some(false);
            }
            let AletheTerm::App(head, args) = &lit.atom else {
                return Some(false);
            };
            if head != "=" || args.len() != 2 {
                return Some(false);
            }
            let inner_is_const_diseq = matches!(
                &args[0],
                AletheTerm::App(h, a)
                    if h == "="
                        && a.len() == 2
                        && matches!(&a[0], AletheTerm::Const(_))
                        && matches!(&a[1], AletheTerm::Const(_))
                        && a[0] != a[1]
            );
            let rhs_is_false = matches!(&args[1], AletheTerm::Const(c) if c == "false");
            Some(inner_is_const_diseq && rhs_is_false)
        }
        // `(cl (not false))` — the `false` tautology.
        "false" => {
            let [lit] = clause else {
                return Some(false);
            };
            Some(lit.negated && matches!(&lit.atom, AletheTerm::Const(c) if c == "false"))
        }
        _ => None,
    }
}

/// A `step` command with the given id, clause, rule, and premise ids (no args).
fn dt_step(id: &str, clause: Vec<AletheLit>, rule: &str, premises: &[&str]) -> AletheCommand {
    AletheCommand::Step {
        id: id.to_owned(),
        clause,
        rule: rule.to_owned(),
        premises: premises.iter().map(|p| (*p).to_owned()).collect(),
        args: Vec::new(),
    }
}

// =====================================================================
// Constructor INJECTIVITY (gap-analysis Gap 14): `C(x…) = C(y…) ⇒ x_i = y_i`
// (same constructor C) is certified by COMPOSING the certified
// select-over-construct fold with congruence — no field-unification axiom, no
// new datatype rule. A downstream field disequality `x_i != y_i` then closes
// to ⊥.
// =====================================================================

/// Emits a complete, **Carcara-checkable** Alethe refutation of an asserted
/// same-constructor equality `(= (C x…) (C y…))` together with a conflicting
/// field disequality `(not (= x_i y_i))` for some field `i`, or [`None`] when no
/// such pair is present or the assembled proof fails self-validation.
///
/// # The composed proof (`cong` on `sel_i` + the two select folds + `trans`)
///
/// The refutation reuses the certified `select`-over-`construct` fold and adds
/// one congruence lift; for the `i`-th selector `sel_i`:
///
/// 1. `h` (the **trusted premise**): the asserted equality `(= (C x…) (C y…))`;
/// 2. `cong` lifts `h` under the selector head `sel_i`:
///    `(= (sel_i (C x…)) (sel_i (C y…)))`;
/// 3. the two **`select`-over-`construct` folds** (the trusted projection
///    equations the `select` certificate certifies the *use* of):
///    `(= (sel_i (C x…)) x_i)` and `(= (sel_i (C y…)) y_i)`;
/// 4. a single `eq_transitive` chains `x_i = sel_i(C x…) = sel_i(C y…) = y_i` to
///    `(= x_i y_i)`, discharged against the three equalities by `resolution`;
/// 5. `resolution` against the trusted field disequality `(not (= x_i y_i))`
///    closes to the empty clause `(cl)`.
///
/// Every rule (`cong`, `eq_transitive`, `resolution`) is exactly the set the
/// `select` and distinctness certificates already use, all **Carcara-checkable**.
/// The two reserved structural heads `!dtsel_n_i_C` / `!dtcon_n_C` are
/// uninterpreted functions to Carcara (no datatype rule).
///
/// # Trust boundary (honest residual)
///
/// The constructor equality `(= (C x…) (C y…))` stays a **trusted premise**
/// (`h`), the field disequality `(not (= x_i y_i))` stays a trusted premise, and
/// the two `select` folds stay trusted premises (as in the certified `select`
/// collapse). What is **Carcara-certified** is the *injectivity reasoning*: that
/// a same-constructor equality forces each field pair `(= x_i y_i)`, so a
/// conflicting `x_i != y_i` is ⊥. Constructor **acyclicity** (which needs
/// induction) and the **distinct-constructor** case remain **trusted/deferred**
/// and are out of scope. The Lean/kernel reconstruction route for the
/// injectivity collapse is deferred (it composes the deferred `select`-fold
/// reconstruction tail through `cong`), so this certificate is
/// **Carcara-checked only**.
///
/// # Returns
///
/// [`None`] when no `(= (C x…) (C y…))` (same constructor) with a matching
/// conflicting `(not (= x_i y_i))` on a renderable (BV/Bool) field occurs in
/// `assertions`, or when the assembled proof fails its own narrow
/// [`axeyum_cnf::check_alethe`] self-validation.
///
/// # Fragment boundary
///
/// Constructor fields are rendered as residual (`BitVec`/`Bool`) leaves; a
/// datatype-typed (nested) field is skipped. The constructor heads are rendered
/// as **structural applications** `(!dtcon_n_C args…)`, so a **nullary**
/// constructor would render as the empty application `(!dtcon_0_C)`, which the
/// SMT-LIB front-end does not accept — only constructors with at least one
/// argument are in scope. **Distinct-constructor** equalities `(= (C x…) (D y…))`
/// are declined (they need distinctness, not injectivity).
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_dt_injective_alethe_carcara(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    // Find the first asserted `(= (C x…) (C y…))` (same constructor) with a
    // conflicting `(not (= x_i y_i))` on some renderable field index `i`.
    let inj = assertions
        .iter()
        .find_map(|&assertion| match_same_constructor_eq(arena, assertion))
        .and_then(|(ctor, xs, ys)| {
            find_conflicting_field(arena, assertions, ctor, &xs, &ys)
                .map(|index| (ctor, xs, ys, index))
        });
    let (ctor, xs, ys, index) = inj?;

    let proof = build_injectivity_proof(arena, ctor, &xs, &ys, index)?;

    // Self-validate with the narrow injectivity hook (Carcara is the trust anchor).
    matches!(
        check_alethe_with(&proof, &injective_simplify_hook),
        Ok(true)
    )
    .then_some(proof)
}

/// Assembles the `cong(sel_i)` + two select folds + `eq_transitive` + closing
/// `resolution` block for field `index` of `(= (C x…) (C y…))` with the trusted
/// disequality `(not (= x_i y_i))`.
fn build_injectivity_proof(
    arena: &TermArena,
    ctor: ConstructorId,
    xs: &[TermId],
    ys: &[TermId],
    index: u32,
) -> Option<Vec<AletheCommand>> {
    // Render both constructor applications structurally (`!dtcon_n_C …`).
    let lhs_con = construct_alethe(arena, ctor, xs)?;
    let rhs_con = construct_alethe(arena, ctor, ys)?;

    // Selector `sel_i` applied to each side: `(!dtsel_n_i_C <con>)`.
    let sel_lhs = selector_alethe(arena, ctor, index, lhs_con.clone());
    let sel_rhs = selector_alethe(arena, ctor, index, rhs_con.clone());

    let x_i = term_to_alethe(arena, xs[index as usize])?;
    let y_i = term_to_alethe(arena, ys[index as usize])?;
    let field_eq = eq_term(x_i.clone(), y_i.clone());

    let proof = vec![
        // h: the TRUSTED same-constructor equality `(= (C x…) (C y…))`.
        AletheCommand::Assume {
            id: "h".to_owned(),
            clause: vec![pos(eq_term(lhs_con, rhs_con))],
        },
        // cong: lift `h` under the selector head: `(= (sel_i (C x…)) (sel_i (C y…)))`.
        dt_step(
            "cong",
            vec![pos(eq_term(sel_lhs.clone(), sel_rhs.clone()))],
            "cong",
            &["h"],
        ),
        // fold_x: the TRUSTED select fold `(= x_i (sel_i (C x…)))`.
        AletheCommand::Assume {
            id: "fold_x".to_owned(),
            clause: vec![pos(eq_term(x_i.clone(), sel_lhs.clone()))],
        },
        // fold_y: the TRUSTED select fold `(= (sel_i (C y…)) y_i)`.
        AletheCommand::Assume {
            id: "fold_y".to_owned(),
            clause: vec![pos(eq_term(sel_rhs.clone(), y_i.clone()))],
        },
        // diseq: the TRUSTED conflicting field disequality `(not (= x_i y_i))`.
        AletheCommand::Assume {
            id: "diseq".to_owned(),
            clause: vec![neg(field_eq.clone())],
        },
        // chain: `eq_transitive` over `x_i = sel_i(C x…) = sel_i(C y…) = y_i`.
        dt_step(
            "chain",
            vec![
                neg(eq_term(x_i, sel_lhs.clone())),
                neg(eq_term(sel_lhs, sel_rhs.clone())),
                neg(eq_term(sel_rhs, y_i)),
                pos(field_eq.clone()),
            ],
            "eq_transitive",
            &[],
        ),
        // contra: resolve the chain against the three equalities ⇒ `(= x_i y_i)`.
        dt_step(
            "contra",
            vec![pos(field_eq)],
            "resolution",
            &["chain", "fold_x", "cong", "fold_y"],
        ),
        // empty: resolve `(= x_i y_i)` against the trusted `(not (= x_i y_i))` ⇒ `(cl)`.
        dt_step("empty", Vec::new(), "resolution", &["contra", "diseq"]),
    ];
    Some(proof)
}

/// If `assertion` is `(= (C x…) (C y…))` with both sides constructor applications
/// of the **same** constructor `C`, returns `(C, x…, y…)`; else [`None`].
fn match_same_constructor_eq(
    arena: &TermArena,
    assertion: TermId,
) -> Option<(ConstructorId, Vec<TermId>, Vec<TermId>)> {
    let TermNode::App { op: Op::Eq, args } = arena.node(assertion) else {
        return None;
    };
    let &[x, y] = &args[..] else {
        return None;
    };
    let (lhs_ctor, lhs_fields) = as_construct(arena, x)?;
    let (rhs_ctor, rhs_fields) = as_construct(arena, y)?;
    (lhs_ctor == rhs_ctor).then_some((lhs_ctor, lhs_fields, rhs_fields))
}

/// Finds the first field index `i` with a renderable (BV/Bool) field pair such
/// that `assertions` contains a disequality `(not (= x_i y_i))` (in either field
/// order). Returns the index, or [`None`] if no field conflict is asserted.
fn find_conflicting_field(
    arena: &TermArena,
    assertions: &[TermId],
    ctor: ConstructorId,
    xs: &[TermId],
    ys: &[TermId],
) -> Option<u32> {
    let field_count = arena.constructor_fields(ctor).len();
    for i in 0..field_count {
        let x_i = xs[i];
        let y_i = ys[i];
        // Only residual (BV/Bool) field sorts are renderable as Alethe leaves.
        if !matches!(arena.sort_of(x_i), Sort::BitVec(_) | Sort::Bool) {
            continue;
        }
        if assertions
            .iter()
            .any(|&a| is_field_disequality(arena, a, x_i, y_i))
        {
            return u32::try_from(i).ok();
        }
    }
    None
}

/// True when `assertion` is `(not (= x_i y_i))` (either field order).
fn is_field_disequality(arena: &TermArena, assertion: TermId, x_i: TermId, y_i: TermId) -> bool {
    let TermNode::App {
        op: Op::BoolNot,
        args: not_args,
    } = arena.node(assertion)
    else {
        return false;
    };
    let &[inner] = &not_args[..] else {
        return false;
    };
    let TermNode::App {
        op: Op::Eq,
        args: eq_args,
    } = arena.node(inner)
    else {
        return false;
    };
    let &[p, q] = &eq_args[..] else {
        return false;
    };
    (p == x_i && q == y_i) || (p == y_i && q == x_i)
}

/// The structural selector application `(!dtsel_n_i_C <con>)` applying the
/// `index`-th selector of constructor `ctor` (arity `n`) to the already-rendered
/// constructor term `con`.
fn selector_alethe(
    arena: &TermArena,
    ctor: ConstructorId,
    index: u32,
    con: AletheTerm,
) -> AletheTerm {
    let name = arena.constructor_name(ctor);
    let n = arena.constructor_fields(ctor).len();
    AletheTerm::App(format!("!dtsel_{n}_{index}_{name}"), vec![con])
}

/// The narrow self-validation hook for [`prove_qf_dt_injective_alethe_carcara`].
///
/// The injectivity refutation uses only `cong`, `eq_transitive`, and
/// `resolution` — all natively handled by [`axeyum_cnf::check_alethe`]. No
/// `evaluate`/`false` simplification is emitted (unlike distinctness), so this
/// hook defers **every** rule (`None`) to the native checker; it exists so the
/// self-validation matches the distinctness pattern and rejects any future shape
/// the native checker would not handle. Carcara is the external trust anchor.
fn injective_simplify_hook(_rule: &str, _clause: &[AletheLit]) -> Option<bool> {
    None
}
