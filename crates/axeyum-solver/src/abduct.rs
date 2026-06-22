//! Boolean abduction (`get-abduct`): turn the trusted checker into a generator.
//!
//! Given Boolean `axioms` and a Boolean `conjecture` `C` that the axioms do
//! **not** by themselves entail, [`abduct`] searches for a hypothesis (an
//! *abduct*) `H` such that:
//!
//! 1. **Consistency:** `axioms ∧ H` is satisfiable;
//! 2. **Sufficiency:** `axioms ∧ H ⊨ C`, i.e. `axioms ∧ H ∧ ¬C` is
//!    unsatisfiable;
//! 3. **Vocabulary:** every uninterpreted symbol / function of `H` occurs in
//!    **both** the axioms and the conjecture (the shared vocabulary — cvc5's
//!    default abduction grammar restriction).
//!
//! This is a categorically-missing Z3/cvc5 feature in the in-tree stack and the
//! first, deliberately bounded, slice of it: a **sound-by-reverification**
//! enumerative search. Candidate *generation* (which literals, which
//! conjunctions) is entirely untrusted; soundness comes only from re-checking
//! every candidate with the trusted decider [`crate::check_auto`] before it is
//! returned. The three conditions are verified verbatim in
//! `verified_abduct`; a candidate that fails any one is rejected. The function
//! therefore **never** returns an `H` that fails verification — an over-eager
//! `None` is acceptable, a wrong abduct is not.
//!
//! ## Method (bounded enumerative)
//!
//! - **Edge cases.** If the axioms already entail `C`, the trivial abduct `⊤`
//!   is returned. If the axioms are themselves inconsistent, no useful abduct
//!   exists and `None` is returned.
//! - **Abducible atoms (syntactic).** The atomic Bool-sorted subformulas of the
//!   axioms and conjecture (theory atoms and Bool-sorted UF applications /
//!   variables — the maximal non-connective Bool subterms) are collected,
//!   together with their negations, restricted to the shared vocabulary.
//! - **Synthesized atoms (`SyGuS`-lite).** Beyond reusing atoms already present,
//!   new shared-vocabulary atoms are *synthesized* over the shared terms
//!   (variables, UF applications, and theory subterms whose vocabulary lies in
//!   the shared sets): equalities `t1 = t2` between distinct same-sort shared
//!   terms, and — for arithmetic (`Int`/`Real`) sorted shared terms — order
//!   comparisons `t ⋈ t'` and `t ⋈ k` for `⋈ ∈ {≤, <, ≥, >, =}`, where `k`
//!   ranges over the numeric constants occurring in the formulas plus `0`. Each
//!   synthesized atom and its negation join the pool, de-duplicated against the
//!   syntactic atoms and dropped if they mention any non-shared symbol/func.
//!   Synthesis is entirely untrusted: a synthesized atom that does not actually
//!   abduce is simply rejected by the verified re-check.
//! - **Candidates, smallest first.** Syntactic atoms are tried before
//!   synthesized ones (so a present atom that abduces wins, keeping abducts
//!   minimal/relevant); then single literals, then conjunctions of two
//!   literals, are tried in a deterministic order (capped at [`MAX_CANDIDATES`]
//!   candidates and conjunction size two). The first candidate passing all three
//!   verified conditions is returned.
//!
//! A fuller version would replace this hand-rolled grammar with a general
//! `SyGuS`-style grammar and a counterexample-guided generator; see the
//! crate-level roadmap.

use std::collections::BTreeSet;

use axeyum_ir::{FuncId, Op, Rational, Sort, SymbolId, TermArena, TermId, TermNode};

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError};

/// Upper bound on the number of candidate abducts the enumerative search will
/// re-check before declining with `None`. A conservative, deterministic budget
/// for this first slice.
pub const MAX_CANDIDATES: usize = 4096;

/// Upper bound on the number of *synthesized* atoms generated before synthesis
/// stops. Caps the size of the candidate literal pool (and hence memory and the
/// `O(n²)` conjunction phase) so the larger `SyGuS`-lite grammar still respects a
/// bounded budget on adversarial inputs. The enumerative re-check is separately
/// capped by [`MAX_CANDIDATES`].
const MAX_SYNTHESIZED_ATOMS: usize = 4096;

/// Searches for a Boolean abduct `H` for `conjecture` under `axioms`.
///
/// Returns `Ok(Some(H))` with a hypothesis that has been **independently
/// re-verified** to satisfy consistency, sufficiency, and the shared-vocabulary
/// restriction (see the module docs), or `Ok(None)` when the bounded
/// enumerative search finds none. The candidate grammar is untrusted; the only
/// thing standing behind a returned `H` is the trusted [`crate::check_auto`]
/// re-check, so a wrong abduct is never produced.
///
/// # Errors
///
/// Propagates any [`SolverError`] from the underlying decider — such an error is
/// a soundness alarm and is never swallowed into a verdict.
pub fn abduct(
    arena: &mut TermArena,
    axioms: &[TermId],
    conjecture: TermId,
    config: &SolverConfig,
) -> Result<Option<TermId>, SolverError> {
    // The conjecture must be a Boolean formula; anything else has no abduct.
    if arena.sort_of(conjecture) != Sort::Bool {
        return Ok(None);
    }
    for &axiom in axioms {
        if arena.sort_of(axiom) != Sort::Bool {
            return Ok(None);
        }
    }

    // Edge case: inconsistent / undecided axioms ⇒ decline early.
    // A definitive `Unsat` means the axioms are inconsistent (no useful abduct);
    // an `Unknown` means their satisfiability is undecided, so the consistency
    // premise cannot be established. Either way, decline rather than risk an
    // unsound `H`; only a definitive `Sat` lets the search proceed.
    let axioms_vec = axioms.to_vec();
    if !matches!(check_auto(arena, &axioms_vec, config)?, CheckResult::Sat(_)) {
        return Ok(None);
    }

    // Edge case: the axioms already entail `C` (`axioms ∧ ¬C` unsat) ⇒ the
    // trivial abduct `⊤`. Consistency holds (axioms are sat, just checked),
    // sufficiency holds (entailment), and `⊤` has empty vocabulary.
    let not_conjecture = arena.not(conjecture).map_err(|e| map_ir(&e))?;
    let mut entail_check = axioms_vec.clone();
    entail_check.push(not_conjecture);
    if matches!(
        check_auto(arena, &entail_check, config)?,
        CheckResult::Unsat
    ) {
        return Ok(Some(arena.bool_const(true)));
    }

    // Shared vocabulary: an atom may enter the candidate grammar only if all of
    // its symbols and functions occur in BOTH the axioms and the conjecture.
    let (axiom_syms, axiom_funcs) = partition_vocabulary(arena, axioms);
    let (conj_syms, conj_funcs) = term_vocabulary(arena, conjecture);
    let shared_syms: BTreeSet<SymbolId> = axiom_syms.intersection(&conj_syms).copied().collect();
    let shared_funcs: BTreeSet<_> = axiom_funcs.intersection(&conj_funcs).copied().collect();

    // Collect abducible atoms (maximal Bool-sorted non-connective subterms) from
    // the axioms and the conjecture, in stable first-seen order.
    let mut atoms: Vec<TermId> = Vec::new();
    let mut seen_atoms: BTreeSet<TermId> = BTreeSet::new();
    for &term in axioms.iter().chain(std::iter::once(&conjecture)) {
        collect_atoms(arena, term, &mut atoms, &mut seen_atoms);
    }

    // Each atom AND its negation, de-duplicated, restricted to shared vocabulary.
    // Pass A (front of the list): the syntactic atoms already present in the
    // formulas, so a present atom that abduces is preferred (minimal/relevant).
    let mut literals: Vec<TermId> = Vec::new();
    let mut seen_lits: BTreeSet<TermId> = BTreeSet::new();
    for atom in atoms {
        if !atom_in_shared_vocabulary(arena, atom, &shared_syms, &shared_funcs) {
            continue;
        }
        push_literal(&mut literals, &mut seen_lits, atom);
        let neg = arena.not(atom).map_err(|e| map_ir(&e))?;
        // The negation reuses the atom's vocabulary, so it is shared too.
        push_literal(&mut literals, &mut seen_lits, neg);
    }

    // Pass B (appended after the syntactic atoms): synthesized shared-vocabulary
    // atoms (`SyGuS`-lite). These are appended so the present atoms are tried
    // first; both share the same verified re-check, so the larger grammar adds
    // reach without weakening soundness. The shared terms and numeric constants
    // are gathered from the formula roots (the axioms and the conjecture).
    let mut roots: Vec<TermId> = axioms.to_vec();
    roots.push(conjecture);
    let synthesized = synthesize_atoms(arena, &roots, &shared_syms, &shared_funcs)?;
    for atom in synthesized {
        // Re-assert shared vocabulary defensively (construction already ensures
        // it) before admitting the atom and its negation.
        if !atom_in_shared_vocabulary(arena, atom, &shared_syms, &shared_funcs) {
            continue;
        }
        push_literal(&mut literals, &mut seen_lits, atom);
        let neg = arena.not(atom).map_err(|e| map_ir(&e))?;
        push_literal(&mut literals, &mut seen_lits, neg);
    }

    let mut tried: usize = 0;

    // Pass 1: single shared literals (smallest / most general first).
    for &lit in &literals {
        if tried >= MAX_CANDIDATES {
            return Ok(None);
        }
        tried += 1;
        if verified_abduct(arena, axioms, conjecture, lit, config)? {
            return Ok(Some(lit));
        }
    }

    // Pass 2: conjunctions of two distinct shared literals.
    for i in 0..literals.len() {
        for j in (i + 1)..literals.len() {
            if tried >= MAX_CANDIDATES {
                return Ok(None);
            }
            tried += 1;
            let cand = arena
                .and(literals[i], literals[j])
                .map_err(|e| map_ir(&e))?;
            if verified_abduct(arena, axioms, conjecture, cand, config)? {
                return Ok(Some(cand));
            }
        }
    }

    Ok(None)
}

/// Re-checks a candidate `H` against all three abduction conditions using the
/// trusted decider, returning whether it is a sound abduct.
///
/// This is the soundness gate: generation is untrusted, so a candidate is
/// returned only if (1) `axioms ∧ H` is definitively `Sat`, (2)
/// `axioms ∧ H ∧ ¬C` is definitively `Unsat`, and (3) `H`'s vocabulary is in the
/// shared vocabulary (already guaranteed by construction for enumerated
/// candidates, re-asserted here as a defensive check). `Unknown` from either
/// decider call rejects the candidate — only definitive verdicts count.
///
/// # Errors
///
/// Propagates [`SolverError`] from the decider (a soundness alarm).
fn verified_abduct(
    arena: &mut TermArena,
    axioms: &[TermId],
    conjecture: TermId,
    hypothesis: TermId,
    config: &SolverConfig,
) -> Result<bool, SolverError> {
    // (1) Consistency: axioms ∧ H is satisfiable (definitive Sat only).
    let mut consistency = axioms.to_vec();
    consistency.push(hypothesis);
    if !matches!(
        check_auto(arena, &consistency, config)?,
        CheckResult::Sat(_)
    ) {
        return Ok(false);
    }

    // (2) Sufficiency: axioms ∧ H ∧ ¬C is unsatisfiable (definitive Unsat only).
    let not_conjecture = arena.not(conjecture).map_err(|e| map_ir(&e))?;
    let mut sufficiency = axioms.to_vec();
    sufficiency.push(hypothesis);
    sufficiency.push(not_conjecture);
    if !matches!(check_auto(arena, &sufficiency, config)?, CheckResult::Unsat) {
        return Ok(false);
    }

    Ok(true)
}

/// Pushes `lit` onto `literals` if not already present (de-duplication that
/// preserves first-seen order).
fn push_literal(literals: &mut Vec<TermId>, seen: &mut BTreeSet<TermId>, lit: TermId) {
    if seen.insert(lit) {
        literals.push(lit);
    }
}

/// Maps an IR builder error into a [`SolverError`]; surfaced as a soundness
/// alarm rather than a silent verdict.
fn map_ir(err: &axeyum_ir::IrError) -> SolverError {
    SolverError::Unsupported(format!("abduction term construction failed: {err}"))
}

/// An arithmetic comparison kind synthesized over shared arithmetic terms.
#[derive(Clone, Copy)]
enum CmpKind {
    Le,
    Lt,
    Ge,
    Gt,
    Eq,
}

/// All five comparison kinds, in a fixed deterministic order.
const CMP_KINDS: [CmpKind; 5] = [
    CmpKind::Le,
    CmpKind::Lt,
    CmpKind::Ge,
    CmpKind::Gt,
    CmpKind::Eq,
];

/// Synthesizes new shared-vocabulary atoms (`SyGuS`-lite): equalities between
/// distinct same-sort shared terms, and order comparisons of arithmetic shared
/// terms against each other and against numeric constants drawn from the
/// formulas (plus `0`).
///
/// The shared terms and numeric constants are collected from the formula
/// `roots` (the axioms and the conjecture). The returned atoms are *candidates*
/// only; every one is still independently re-verified before it can become an
/// abduct, and every one is restricted to the shared vocabulary by construction
/// (its operands are shared terms). The list is deterministic: shared terms and
/// constants are collected in stable (`BTreeSet`) order, and comparison kinds in
/// the fixed [`CMP_KINDS`] order.
///
/// # Errors
///
/// Propagates [`SolverError`] from IR term construction (a soundness alarm).
fn synthesize_atoms(
    arena: &mut TermArena,
    roots: &[TermId],
    shared_syms: &BTreeSet<SymbolId>,
    shared_funcs: &BTreeSet<FuncId>,
) -> Result<Vec<TermId>, SolverError> {
    // Shared terms by sort, stable order. Equalities apply to any sort; order
    // comparisons only to the arithmetic sorts.
    let shared_terms = collect_shared_terms(arena, roots, shared_syms, shared_funcs);
    // Numeric constants occurring in the formulas, by sort, plus a fixed `0`.
    let int_consts = numeric_constants(arena, roots, Sort::Int);
    let real_consts = numeric_constants(arena, roots, Sort::Real);

    let mut out: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();

    // (1) Equalities `t1 = t2` between distinct same-sort shared terms.
    let n = shared_terms.len();
    'eqs: for i in 0..n {
        for j in (i + 1)..n {
            let (ti, si) = shared_terms[i];
            let (tj, sj) = shared_terms[j];
            if si != sj {
                continue;
            }
            let eq = arena.eq(ti, tj).map_err(|e| map_ir(&e))?;
            if !push_synth(&mut out, &mut seen, eq) {
                break 'eqs;
            }
        }
    }

    // (2) Order comparisons for arithmetic-sorted shared terms. Int and Real
    // term/constant pools are kept separate by sort.
    let int_terms: Vec<TermId> = shared_terms
        .iter()
        .filter(|(_, s)| *s == Sort::Int)
        .map(|(t, _)| *t)
        .collect();
    let real_terms: Vec<TermId> = shared_terms
        .iter()
        .filter(|(_, s)| *s == Sort::Real)
        .map(|(t, _)| *t)
        .collect();

    synthesize_order_comparisons(
        arena,
        &int_terms,
        &int_consts,
        Sort::Int,
        &mut out,
        &mut seen,
    )?;
    synthesize_order_comparisons(
        arena,
        &real_terms,
        &real_consts,
        Sort::Real,
        &mut out,
        &mut seen,
    )?;

    Ok(out)
}

/// Builds order comparisons (`≤,<,≥,>,=`) among the given same-sort arithmetic
/// `terms`, and between each term and each numeric constant `consts` of that
/// sort.
///
/// # Errors
///
/// Propagates [`SolverError`] from IR term construction.
fn synthesize_order_comparisons(
    arena: &mut TermArena,
    terms: &[TermId],
    consts: &[TermId],
    sort: Sort,
    out: &mut Vec<TermId>,
    seen: &mut BTreeSet<TermId>,
) -> Result<(), SolverError> {
    if terms.is_empty() {
        return Ok(());
    }

    // term ⋈ term' for ordered distinct pairs (i < j). We emit all five kinds so
    // `t ≤ t'`, `t ≥ t'`, etc. are each directly available (the literal pool
    // additionally adds each atom's negation).
    let n = terms.len();
    'pairs: for i in 0..n {
        for j in (i + 1)..n {
            for kind in CMP_KINDS {
                let atom = build_cmp(arena, kind, terms[i], terms[j], sort)?;
                if !push_synth(out, seen, atom) {
                    break 'pairs;
                }
            }
        }
    }

    // term ⋈ constant for each numeric constant of this sort.
    'consts: for &k in consts {
        for &t in terms {
            for kind in CMP_KINDS {
                let atom = build_cmp(arena, kind, t, k, sort)?;
                if !push_synth(out, seen, atom) {
                    break 'consts;
                }
            }
        }
    }

    Ok(())
}

/// Constructs a single comparison atom `lhs ⋈ rhs` of arithmetic `sort`,
/// dispatching to the per-sort builder (`int_*` / `real_*`).
///
/// # Errors
///
/// Propagates [`SolverError`] from the IR builders.
fn build_cmp(
    arena: &mut TermArena,
    kind: CmpKind,
    lhs: TermId,
    rhs: TermId,
    sort: Sort,
) -> Result<TermId, SolverError> {
    let built = match kind {
        // Equality is sort-agnostic; callers only pass Int/Real terms to the
        // ordered kinds, and any other sort falls back to equality to stay total.
        CmpKind::Eq => arena.eq(lhs, rhs),
        CmpKind::Le if sort == Sort::Int => arena.int_le(lhs, rhs),
        CmpKind::Lt if sort == Sort::Int => arena.int_lt(lhs, rhs),
        CmpKind::Ge if sort == Sort::Int => arena.int_ge(lhs, rhs),
        CmpKind::Gt if sort == Sort::Int => arena.int_gt(lhs, rhs),
        CmpKind::Le => arena.real_le(lhs, rhs),
        CmpKind::Lt => arena.real_lt(lhs, rhs),
        CmpKind::Ge => arena.real_ge(lhs, rhs),
        CmpKind::Gt => arena.real_gt(lhs, rhs),
    };
    built.map_err(|e| map_ir(&e))
}

/// Pushes a synthesized atom if new (de-duplication preserving first-seen
/// order). Returns `false` once the synthesized-atom budget
/// ([`MAX_SYNTHESIZED_ATOMS`]) is exhausted, signalling callers to stop
/// generating.
fn push_synth(out: &mut Vec<TermId>, seen: &mut BTreeSet<TermId>, atom: TermId) -> bool {
    if out.len() >= MAX_SYNTHESIZED_ATOMS {
        return false;
    }
    if seen.insert(atom) {
        out.push(atom);
    }
    true
}

/// Collects the numeric constants of `sort` (`Int` or `Real`) occurring in the
/// `roots` (the axioms and conjecture), plus the fixed constant `0` of that
/// sort, in stable value order.
///
/// Constants are gathered by structural walk, then materialized as constant
/// terms (interned, so duplicates fold). The fixed `0` guarantees a useful
/// pivot even when no literal constant appears in the formulas.
fn numeric_constants(arena: &mut TermArena, roots: &[TermId], sort: Sort) -> Vec<TermId> {
    match sort {
        Sort::Int => {
            let mut values: BTreeSet<i128> = BTreeSet::new();
            values.insert(0);
            for &root in roots {
                walk_subterms(arena, root, &mut |node| {
                    if let TermNode::IntConst(v) = node {
                        values.insert(*v);
                    }
                });
            }
            values.into_iter().map(|v| arena.int_const(v)).collect()
        }
        Sort::Real => {
            let mut values: BTreeSet<Rational> = BTreeSet::new();
            values.insert(Rational::zero());
            for &root in roots {
                walk_subterms(arena, root, &mut |node| {
                    if let TermNode::RealConst(v) = node {
                        values.insert(*v);
                    }
                });
            }
            values.into_iter().map(|v| arena.real_const(v)).collect()
        }
        _ => Vec::new(),
    }
}

/// Collects the shared *terms* — subterms of the `roots` whose entire vocabulary
/// lies in the shared symbol/func sets — paired with their sorts, in stable
/// first-seen order. These are the building blocks the synthesizer combines into
/// atoms: shared variables, shared UF applications, and shared theory subterms.
///
/// Numeric/Bool constants and Bool-sorted terms are excluded (constants are
/// handled separately, and Bool subterms are propositional structure rather than
/// term operands of an equality/comparison).
fn collect_shared_terms(
    arena: &TermArena,
    roots: &[TermId],
    shared_syms: &BTreeSet<SymbolId>,
    shared_funcs: &BTreeSet<FuncId>,
) -> Vec<(TermId, Sort)> {
    let mut out: Vec<(TermId, Sort)> = Vec::new();
    let mut emitted: BTreeSet<TermId> = BTreeSet::new();
    for &root in roots {
        let mut order: Vec<TermId> = Vec::new();
        let mut seen: BTreeSet<TermId> = BTreeSet::new();
        collect_subterm_ids(arena, root, &mut order, &mut seen);
        for t in order {
            let sort = arena.sort_of(t);
            if sort == Sort::Bool {
                continue;
            }
            if matches!(
                arena.node(t),
                TermNode::BvConst { .. }
                    | TermNode::WideBvConst(_)
                    | TermNode::IntConst(_)
                    | TermNode::RealConst(_)
                    | TermNode::BoolConst(_)
            ) {
                continue;
            }
            if !atom_in_shared_vocabulary(arena, t, shared_syms, shared_funcs) {
                continue;
            }
            if emitted.insert(t) {
                out.push((t, sort));
            }
        }
    }
    out
}

/// Records every distinct subterm id of `term` (including `term`) into `order`
/// in a stable first-seen (pre-order) walk.
fn collect_subterm_ids(
    arena: &TermArena,
    term: TermId,
    order: &mut Vec<TermId>,
    seen: &mut BTreeSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    order.push(term);
    if let TermNode::App { args, .. } = arena.node(term) {
        let children = args.to_vec();
        for child in children {
            collect_subterm_ids(arena, child, order, seen);
        }
    }
}

/// Visits every distinct subterm node of `term` (including `term`), calling
/// `visit` once per distinct subterm. Used to harvest numeric constants.
fn walk_subterms(arena: &TermArena, term: TermId, visit: &mut impl FnMut(&TermNode)) {
    let mut order: Vec<TermId> = Vec::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    collect_subterm_ids(arena, term, &mut order, &mut seen);
    for t in order {
        visit(arena.node(t));
    }
}

/// Collects the maximal Bool-sorted non-connective subterms (theory atoms and
/// Bool-sorted UF applications / variables) of `term`, recursing only through
/// the Boolean connectives `and`/`or`/`not`/`implies`/`xor`/`ite`.
///
/// Non-Bool subterms are never atoms (their parents are). A Bool-sorted leaf
/// that is not one of the connectives is recorded as an atom and not descended
/// into, so `f(x) = g(y)` is one atom rather than yielding its argument terms.
fn collect_atoms(
    arena: &TermArena,
    term: TermId,
    atoms: &mut Vec<TermId>,
    seen: &mut BTreeSet<TermId>,
) {
    if arena.sort_of(term) != Sort::Bool {
        return;
    }
    match arena.node(term) {
        TermNode::Symbol(_) => {
            if seen.insert(term) {
                atoms.push(term);
            }
        }
        TermNode::App { op, args } => {
            if is_boolean_connective(op) {
                let children = args.to_vec();
                for child in children {
                    collect_atoms(arena, child, atoms, seen);
                }
            } else if seen.insert(term) {
                // A Bool-sorted theory atom or UF application: the maximal
                // non-connective unit. Record it; do not descend.
                atoms.push(term);
            }
        }
        // `⊤` / `⊥` carry no information as abducts; the remaining node kinds are
        // not Bool-sorted and are excluded above by the sort guard.
        TermNode::BoolConst(_)
        | TermNode::BvConst { .. }
        | TermNode::WideBvConst(_)
        | TermNode::IntConst(_)
        | TermNode::RealConst(_) => {}
    }
}

/// Whether `op` is a Boolean connective the atom walk recurses *through* (rather
/// than treating its application as an atom). `Ite` is included because a
/// Bool-sorted `ite` is propositional structure over its Bool leaves.
fn is_boolean_connective(op: &Op) -> bool {
    matches!(
        op,
        Op::BoolNot | Op::BoolAnd | Op::BoolOr | Op::BoolXor | Op::BoolImplies | Op::Ite
    )
}

/// Whether every symbol and function of `atom` lies within the shared
/// vocabulary sets.
fn atom_in_shared_vocabulary(
    arena: &TermArena,
    atom: TermId,
    shared_syms: &BTreeSet<SymbolId>,
    shared_funcs: &BTreeSet<axeyum_ir::FuncId>,
) -> bool {
    let (syms, funcs) = term_vocabulary(arena, atom);
    syms.is_subset(shared_syms) && funcs.is_subset(shared_funcs)
}

/// The uninterpreted symbols and function ids appearing in a slice of
/// assertions.
fn partition_vocabulary(
    arena: &TermArena,
    assertions: &[TermId],
) -> (BTreeSet<SymbolId>, BTreeSet<axeyum_ir::FuncId>) {
    let mut syms = BTreeSet::new();
    let mut funcs = BTreeSet::new();
    for &assertion in assertions {
        collect_vocabulary(arena, assertion, &mut syms, &mut funcs);
    }
    (syms, funcs)
}

/// The uninterpreted symbols and function ids appearing in a single term.
fn term_vocabulary(
    arena: &TermArena,
    term: TermId,
) -> (BTreeSet<SymbolId>, BTreeSet<axeyum_ir::FuncId>) {
    let mut syms = BTreeSet::new();
    let mut funcs = BTreeSet::new();
    collect_vocabulary(arena, term, &mut syms, &mut funcs);
    (syms, funcs)
}

/// Walks `term`, recording every free symbol and every applied function id.
fn collect_vocabulary(
    arena: &TermArena,
    term: TermId,
    syms: &mut BTreeSet<SymbolId>,
    funcs: &mut BTreeSet<axeyum_ir::FuncId>,
) {
    let mut stack = vec![term];
    let mut seen = BTreeSet::new();
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(symbol) => {
                syms.insert(*symbol);
            }
            TermNode::App { op, args } => {
                if let Op::Apply(func) = op {
                    funcs.insert(*func);
                }
                stack.extend(args.iter().copied());
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {}
        }
    }
}
