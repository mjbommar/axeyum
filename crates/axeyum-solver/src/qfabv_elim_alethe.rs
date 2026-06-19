//! Alethe proof **emission** for `QF_ABV` refutations decided via the
//! **array-elimination reduction** (Track 3, phase P3.5 — ADR-0010 task #20).
//!
//! [`prove_qf_abv_unsat_alethe_via_elimination`] closes the last trusted step
//! under an array-elimination-decided `unsat`. The reduction
//! ([`axeyum_rewrite::eliminate_arrays`]) does two things:
//!
//! 1. **Read-over-write.** `select(store(a, i, v), j)` rewrites to
//!    `ite(i = j, v, select(a, j))`, until every remaining `select` reads an
//!    array *variable*.
//! 2. **Ackermann-over-select.** Each distinct `select(a, idx)` on an array
//!    variable `a` is abstracted to a fresh `BitVec` symbol `s`, and for each
//!    pair of selects on the same `a` a **read-consistency constraint**
//!    `(i = j) -> (s_i = s_j)` is added — exactly functional consistency of
//!    `select(a, ·)` treated as an uninterpreted function.
//!
//! The bit-blasting back-end then refutes the reduced `QF_BV` formula, but the
//! read-consistency constraints were, until now, *trusted*: the reduced
//! refutation simply assumed them. They are not axioms. Treating `select(a, ·)`
//! as a fresh **unary uninterpreted function** `sel_a` — with `s_i = sel_a(i)`
//! its abstraction definition — each consistency constraint is exactly an
//! `eq_congruent` instance over `sel_a`, so it is **derivable**, not assumed.
//! That derivation is the certificate this module supplies.
//!
//! ## Relationship to the `QF_UFBV` certificate
//!
//! This is the array specialisation of [`crate::prove_qf_ufbv_unsat_alethe`]: an
//! array variable `a` *is* an uninterpreted unary function `sel_a := λ idx.
//! select(a, idx)`, and Ackermann-over-select *is* Ackermann-over-functions for
//! that `sel_a`. The emitter therefore produces the **same** spliced `!cong_*`
//! congruence-block shape, so the very same reconstructor
//! ([`crate::reconstruct_qf_ufbv_proof`]) reconstructs the resulting proof to a
//! kernel-checked `False` with no trusted reduction step.
//!
//! The current emitter certifies the **read-consistency** stratum (the
//! Ackermann-over-select trust hole). It applies to array-elimination instances
//! whose refutation rests on select congruence (no per-query read-over-write
//! *store* rewrite is needed); the read-over-write-same fragment has its own
//! dedicated certificate in [`crate::prove_qf_abv_unsat_alethe`]. The emitter
//! declines (returns [`None`]) when the reduced problem requires store rewrites
//! it cannot yet justify, falling outside its fragment.
//!
//! Emission is **self-validating**: the assembled proof is run through
//! [`axeyum_cnf::check_alethe`] before return, so a returned certificate is
//! always checkable; the external Carcara binary is the trust anchor for the
//! `eq_congruent`/bit-blast parts (Carcara has no array rules, but this
//! certificate uses none — `select(a, ·)` is a plain uninterpreted function).

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe};
use axeyum_ir::{Op, SymbolId, TermArena, TermId, TermNode};

/// One read-consistency constraint whose consequent `(= s_i s_j)` the reduced
/// refutation assumes, with the data to derive it by `eq_congruent` over the
/// per-array unary function `sel_a`.
struct SelectCongruenceCert {
    /// The fresh abstraction symbol for select `i` (renders as `s_i`).
    fresh_i: SymbolId,
    /// The fresh abstraction symbol for select `j`.
    fresh_j: SymbolId,
    /// The (rewritten) index term of select `i`.
    index_i: TermId,
    /// The (rewritten) index term of select `j`.
    index_j: TermId,
    /// The synthetic unary-function name `sel_<array>` shared by both selects.
    sel_name: String,
}

/// Emits a complete, checkable Alethe refutation for an `unsat` `QF_ABV`
/// conjunction decided by the array-elimination reduction — with every
/// **read-consistency** (Ackermann-over-select) constraint **proven** by
/// `eq_congruent` over the per-array unary select function rather than assumed —
/// or [`None`] when the query has no arrays, the reduced `QF_BV` problem is
/// outside the bit-blast-emitter fragment, the refutation does not rest on a
/// derivable read-consistency constraint, or the assembled proof fails
/// self-validation.
///
/// Requires `&mut TermArena` because the array-elimination reduction interns
/// fresh abstraction symbols and the consequent equalities `(= s_i s_j)`.
///
/// The certificate is sound: the consistency constraint `(i = j) -> (s_i = s_j)`
/// is derived from the index equality and the abstraction's defining equations
/// `(= s_i (sel_a i))` (conservative fresh-variable introductions, where
/// `sel_a := λ idx. select(a, idx)`), so no reduction step is trusted. The
/// returned proof closes to `(cl)` and has been accepted by
/// [`axeyum_cnf::check_alethe`] before return; it carries the same `!cong_*`
/// congruence-block shape as the `QF_UFBV` certificate, so
/// [`crate::reconstruct_qf_ufbv_proof`] reconstructs it to a kernel-checked
/// `False`.
///
/// Returns [`None`] when:
///
/// - the conjunction contains no array constructs (use
///   [`crate::prove_qf_bv_unsat_alethe`] directly);
/// - the reduced `QF_BV` conjunction (rewritten originals plus the derivable
///   consistency consequents) is outside the fragment the bit-blast emitter
///   handles, or is not genuinely `unsat`;
/// - no read-consistency constraint's index equality is directly available, so
///   no consequent is derivable by a single `eq_congruent`; or
/// - the assembled proof fails its own [`axeyum_cnf::check_alethe`] re-check.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_abv_unsat_alethe_via_elimination(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    let elim = axeyum_rewrite::eliminate_arrays(arena, assertions).ok()?;
    if !elim.had_arrays() {
        return None;
    }

    // The rewritten-only (abstraction) assertions — no consistency lemmas yet.
    let rewritten = elim.abstraction().to_vec();

    // The eliminated selects: `(array symbol, index term, fresh result symbol)`.
    let selects = elim.selects();
    if selects.len() < 2 {
        return None;
    }

    // The index equalities the rewritten originals directly assert, as an
    // unordered set of `{a, b}` term-id pairs, and the undirected graph they induce
    // (so an index equality holding only by *transitive closure* — `i=k ∧ k=j` —
    // still discharges a read-consistency antecedent, via an `eq_transitive` chain).
    let asserted_eqs = collect_asserted_eqs(arena, &rewritten);
    let adjacency = asserted_eq_adjacency(&asserted_eqs);

    // For every pair of selects on the **same array** whose indices are equal
    // (identically, directly, or by transitive closure), the consequent
    // `(= s_i s_j)` is `eq_congruent`-derivable over the unary function `sel_<array>`.
    let mut certs: Vec<SelectCongruenceCert> = Vec::new();
    for i in 0..selects.len() {
        for j in (i + 1)..selects.len() {
            let (array_i, index_i, fresh_i) = selects[i];
            let (array_j, index_j, fresh_j) = selects[j];
            if array_i != array_j {
                continue;
            }
            let indices_equal =
                index_i == index_j || eq_path(&adjacency, index_i, index_j).is_some();
            if indices_equal {
                let (array_name, _) = arena.symbol(array_i);
                certs.push(SelectCongruenceCert {
                    fresh_i,
                    fresh_j,
                    index_i,
                    index_j,
                    sel_name: format!("!sel_{array_name}"),
                });
            }
        }
    }
    if certs.is_empty() {
        return None;
    }

    // The reduced QF_BV problem: rewritten originals plus the consistency
    // *consequents* `(= s_i s_j)` (the antecedents are discharged by the asserted
    // index equalities, so the unconditional consequent is sound to add).
    let mut bv_assertions = rewritten.clone();
    let mut consequent_terms: Vec<(TermId, SymbolId, SymbolId)> = Vec::new();
    for cert in &certs {
        let si = arena.var(cert.fresh_i);
        let sj = arena.var(cert.fresh_j);
        let eq = arena.eq(si, sj).ok()?;
        bv_assertions.push(eq);
        consequent_terms.push((eq, cert.fresh_i, cert.fresh_j));
    }

    // Bit-blast refutation of the reduced QF_BV problem. It `assume`s each
    // consequent `(= s_i s_j)`.
    let bv_proof = crate::prove_qf_bv_unsat_alethe_lowered(arena, &bv_assertions)?;

    // Splice: replace each consequent's `Assume` with its `eq_congruent`
    // derivation under the same id, so the read-consistency constraint is proven.
    let spliced =
        splice_select_congruence(arena, &bv_proof, &certs, &consequent_terms, &adjacency)?;

    // Self-validate before returning.
    if matches!(check_alethe(&spliced), Ok(true)) {
        Some(spliced)
    } else {
        None
    }
}

/// Collects the directly-asserted equalities among the rewritten originals as an
/// unordered set of `{a, b}` term-id pairs.
fn collect_asserted_eqs(arena: &TermArena, rewritten: &[TermId]) -> BTreeSet<(TermId, TermId)> {
    let mut set = BTreeSet::new();
    for &t in rewritten {
        if let TermNode::App { op: Op::Eq, args } = arena.node(t)
            && let [a, b] = &args[..]
        {
            set.insert(ordered(*a, *b));
        }
    }
    set
}

/// Canonical unordered pair (smaller id first).
fn ordered(a: TermId, b: TermId) -> (TermId, TermId) {
    if a.index() <= b.index() {
        (a, b)
    } else {
        (b, a)
    }
}

/// The undirected adjacency map induced by a set of asserted equalities, for
/// transitive-closure index reasoning (mirrors the `QF_UFBV` certificate helper).
fn asserted_eq_adjacency(asserted: &BTreeSet<(TermId, TermId)>) -> BTreeMap<TermId, Vec<TermId>> {
    let mut adj: BTreeMap<TermId, Vec<TermId>> = BTreeMap::new();
    for &(a, b) in asserted {
        adj.entry(a).or_default().push(b);
        adj.entry(b).or_default().push(a);
    }
    adj
}

/// The shortest path `from = t0, …, tn = to` of asserted-equality edges (BFS), or
/// [`None`] if disconnected. A returned path has `len() >= 2` (never the trivial
/// `from == to` path; identical indices are handled separately by the caller).
fn eq_path(
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
    from: TermId,
    to: TermId,
) -> Option<Vec<TermId>> {
    if from == to {
        return None;
    }
    let mut prev: BTreeMap<TermId, TermId> = BTreeMap::new();
    let mut queue: std::collections::VecDeque<TermId> = std::collections::VecDeque::new();
    let mut seen: BTreeSet<TermId> = BTreeSet::new();
    queue.push_back(from);
    seen.insert(from);
    while let Some(node) = queue.pop_front() {
        if node == to {
            let mut path = vec![to];
            let mut cur = to;
            while cur != from {
                cur = prev[&cur];
                path.push(cur);
            }
            path.reverse();
            return Some(path);
        }
        if let Some(neighbours) = adjacency.get(&node) {
            for &next in neighbours {
                if seen.insert(next) {
                    prev.insert(next, node);
                    queue.push_back(next);
                }
            }
        }
    }
    None
}

/// Replaces each consequent `(= s_i s_j)` `Assume` in `bv_proof` with an
/// `eq_congruent` derivation of `(cl (= s_i s_j))` under the same id, so the
/// read-consistency constraint is proven from the index equality and the
/// abstraction's defining equations rather than assumed. The spliced commands
/// use the `!cong_*` id namespace, matching the `QF_UFBV` certificate, so
/// [`crate::reconstruct_qf_ufbv_proof`] reconstructs the result unchanged.
fn splice_select_congruence(
    arena: &TermArena,
    bv_proof: &[AletheCommand],
    certs: &[SelectCongruenceCert],
    consequents: &[(TermId, SymbolId, SymbolId)],
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
) -> Option<Vec<AletheCommand>> {
    // Map each consequent's `(= s_i s_j)` clause key to its cert.
    let mut by_consequent: BTreeMap<String, &SelectCongruenceCert> = BTreeMap::new();
    for ((_, fi, fj), cert) in consequents.iter().zip(certs.iter()) {
        debug_assert!(*fi == cert.fresh_i && *fj == cert.fresh_j);
        let key = consequent_clause_key(arena, cert.fresh_i, cert.fresh_j);
        by_consequent.insert(key, cert);
    }

    let mut out: Vec<AletheCommand> = Vec::with_capacity(bv_proof.len() + certs.len() * 4);
    let mut fresh = 0usize;
    for cmd in bv_proof {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                if let Some(cert) = clause_consequent_cert(clause, &by_consequent) {
                    emit_select_congruence(arena, &mut out, &mut fresh, id, cert, adjacency)?;
                } else {
                    out.push(cmd.clone());
                }
            }
            step @ AletheCommand::Step { .. } => out.push(step.clone()),
        }
    }
    Some(out)
}

/// If `clause` is a single positive literal `(= s_i s_j)` matching a registered
/// consequent, returns its cert.
fn clause_consequent_cert<'a>(
    clause: &AletheClause,
    by_consequent: &BTreeMap<String, &'a SelectCongruenceCert>,
) -> Option<&'a SelectCongruenceCert> {
    let [lit] = clause.as_slice() else {
        return None;
    };
    if lit.negated {
        return None;
    }
    by_consequent.get(&lit.atom.key()).copied()
}

/// The `(= s_i s_j)` clause key for a consequent (the fresh symbols' names).
fn consequent_clause_key(arena: &TermArena, fi: SymbolId, fj: SymbolId) -> String {
    eq_term(sym_alethe(arena, fi), sym_alethe(arena, fj)).key()
}

/// Emits, under `assume_id`, the steps deriving `(cl (= s_i s_j))` by
/// `eq_congruent` over the unary select function `sel_a` plus `eq_transitive`
/// through the abstraction's defining equations:
///
/// ```text
/// (assume d_def_i  (= s_i (sel_a i)))   ; abstraction definition (conservative)
/// (assume d_def_j  (= (sel_a j) s_j))
/// (assume d_idx    (= i j))             ; original index equality
/// (step   d_cong   (cl (not (= i j)) (= (sel_a i) (sel_a j))) :rule eq_congruent)
/// (step   <assume_id> (cl (= s_i s_j)) :rule resolution …)
/// ```
///
/// The final step is given the original assume's id so every downstream premise
/// referencing the consequent resolves unchanged. The `sel_a` head is a plain
/// unary uninterpreted function (no array rule), so the `eq_congruent` step is
/// Carcara-valid and reconstructs through the EUF head.
fn emit_select_congruence(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    cert: &SelectCongruenceCert,
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
) -> Option<()> {
    let si = sym_alethe(arena, cert.fresh_i);
    let sj = sym_alethe(arena, cert.fresh_j);

    // The index terms `i` and `j` as Alethe terms (symbols / bit-vector consts).
    let idx_i = term_to_alethe(arena, cert.index_i)?;
    let idx_j = term_to_alethe(arena, cert.index_j)?;
    // The applications `(sel_a i)` and `(sel_a j)`.
    let sel_i = AletheTerm::App(cert.sel_name.clone(), vec![idx_i.clone()]);
    let sel_j = AletheTerm::App(cert.sel_name.clone(), vec![idx_j.clone()]);

    // Abstraction definitions, oriented for the transitive chain
    // s_i → sel_a(i) → sel_a(j) → s_j: `(= s_i (sel_a i))` and `(= (sel_a j) s_j)`.
    let def_i = next_id(fresh, "defi");
    out.push(AletheCommand::Assume {
        id: def_i.clone(),
        clause: vec![pos(eq_term(si.clone(), sel_i.clone()))],
    });
    let def_j = next_id(fresh, "defj");
    out.push(AletheCommand::Assume {
        id: def_j.clone(),
        clause: vec![pos(eq_term(sel_j.clone(), sj.clone()))],
    });

    // The index equality unit `(cl (= i j))`: reflexive, a direct asserted edge, or
    // an `eq_transitive` chain over the transitive closure of asserted equalities.
    let idx_eq_id = emit_index_equality_unit(arena, out, fresh, cert, &idx_i, &idx_j, adjacency)?;

    // eq_congruent: (cl (not (= i j)) (= (sel_a i) (sel_a j))), resolved against
    // the index-equality unit → (cl (= (sel_a i) (sel_a j))).
    let cong = next_id(fresh, "eqcong");
    out.push(AletheCommand::Step {
        id: cong.clone(),
        clause: vec![
            neg(eq_term(idx_i.clone(), idx_j.clone())),
            pos(eq_term(sel_i.clone(), sel_j.clone())),
        ],
        rule: "eq_congruent".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    let sel_eq = next_id(fresh, "seleq");
    out.push(AletheCommand::Step {
        id: sel_eq.clone(),
        clause: vec![pos(eq_term(sel_i.clone(), sel_j.clone()))],
        rule: "resolution".to_owned(),
        premises: vec![cong, idx_eq_id],
        args: Vec::new(),
    });

    // Chain s_i = sel_a(i) = sel_a(j) = s_j by a single `eq_transitive` over the
    // two abstraction definitions and the derived `(= (sel_a i) (sel_a j))`.
    let trans = next_id(fresh, "trans");
    out.push(AletheCommand::Step {
        id: trans.clone(),
        clause: vec![
            neg(eq_term(si.clone(), sel_i.clone())),
            neg(eq_term(sel_i, sel_j.clone())),
            neg(eq_term(sel_j, sj.clone())),
            pos(eq_term(si.clone(), sj.clone())),
        ],
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });

    // Final resolution to (cl (= s_i s_j)), under the consequent's assume id.
    out.push(AletheCommand::Step {
        id: assume_id.to_owned(),
        clause: vec![pos(eq_term(si, sj))],
        rule: "resolution".to_owned(),
        premises: vec![trans, def_i, sel_eq, def_j],
        args: Vec::new(),
    });

    Some(())
}

/// Emits the index-equality unit `(cl (= i j))` and returns its step id:
///
/// - `eq_reflexive` for an identical index (`index_i == index_j`);
/// - a direct `assume` of `(= i j)` for a single asserted edge; or
/// - an `eq_transitive` chain (each asserted edge `assume`d, chained with shared
///   middle terms and resolved to `(= i j)`) when `i` and `j` are equal only by
///   transitive closure of the asserted index equalities.
///
/// Returns [`None`] if a transitive-path node is outside the renderable fragment.
fn emit_index_equality_unit(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    cert: &SelectCongruenceCert,
    idx_i: &AletheTerm,
    idx_j: &AletheTerm,
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
) -> Option<String> {
    if cert.index_i == cert.index_j {
        let r = next_id(fresh, "refl");
        out.push(AletheCommand::Step {
            id: r.clone(),
            clause: vec![pos(eq_term(idx_i.clone(), idx_j.clone()))],
            rule: "eq_reflexive".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
        });
        return Some(r);
    }
    let path = eq_path(adjacency, cert.index_i, cert.index_j)?;
    if path.len() == 2 {
        // A single asserted edge `(= i j)`: assume it directly (unchanged).
        let g = next_id(fresh, "idx");
        out.push(AletheCommand::Assume {
            id: g.clone(),
            clause: vec![pos(eq_term(idx_i.clone(), idx_j.clone()))],
        });
        return Some(g);
    }
    // Transitive closure `i = m_1 = … = j`: assume each edge and chain them with one
    // `eq_transitive` step (shared middle terms) resolved to `(= i j)`.
    let nodes: Vec<AletheTerm> = path
        .iter()
        .map(|&n| term_to_alethe(arena, n))
        .collect::<Option<_>>()?;
    let mut edge_ids = Vec::with_capacity(nodes.len() - 1);
    for w in nodes.windows(2) {
        let e = next_id(fresh, "edge");
        out.push(AletheCommand::Assume {
            id: e.clone(),
            clause: vec![pos(eq_term(w[0].clone(), w[1].clone()))],
        });
        edge_ids.push(e);
    }
    let mut trans_clause: AletheClause = nodes
        .windows(2)
        .map(|w| neg(eq_term(w[0].clone(), w[1].clone())))
        .collect();
    trans_clause.push(pos(eq_term(idx_i.clone(), idx_j.clone())));
    let idx_trans = next_id(fresh, "idxtrans");
    out.push(AletheCommand::Step {
        id: idx_trans.clone(),
        clause: trans_clause,
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    let derived = next_id(fresh, "idxeq");
    let mut prems = vec![idx_trans];
    prems.extend(edge_ids);
    out.push(AletheCommand::Step {
        id: derived.clone(),
        clause: vec![pos(eq_term(idx_i.clone(), idx_j.clone()))],
        rule: "resolution".to_owned(),
        premises: prems,
        args: Vec::new(),
    });
    Some(derived)
}

/// A fresh, namespaced derivation-step id (`!cong_<base>_<n>`), matching the
/// `QF_UFBV` certificate's namespace so the shared reconstructor recognises the
/// congruence block.
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

/// Converts an IR term to an [`AletheTerm`] for the index fragment (symbols and
/// bit-vector constants), or [`None`] otherwise.
fn term_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
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
