//! Alethe proof **emission** for `QF_UFBV` refutations decided via the
//! **Ackermann reduction** (Track 3, phase P3.5 — ADR-0013 task #19).
//!
//! [`prove_qf_ufbv_unsat_alethe`] closes the last trusted step under an
//! Ackermann-decided `unsat`: the reduction
//! ([`axeyum_rewrite::eliminate_functions`]) abstracts each application
//! `f(args)` to a fresh scalar symbol `v` and adds **functional-consistency
//! constraints** `(a = b) -> (v_i = v_j)` for two applications of the same `f`.
//! The bit-blasting back-end then refutes the reduced `QF_BV` formula — but the
//! consistency constraints themselves were, until now, *trusted*: the reduced
//! refutation simply assumed them. They are not axioms; each is exactly an
//! `eq_congruent` instance over `f` (with `v_i = f(a_i)` the abstraction's
//! defining equation), so it is **derivable**, not assumed. That derivation is
//! the certificate this module supplies.
//!
//! ## The composed proof
//!
//! The emitter builds a complete, Carcara-checkable Alethe refutation of the
//! **original** `QF_UFBV` conjunction by composing:
//!
//! 1. a **bit-blast refutation** of the reduced `QF_BV` problem — the rewritten
//!    originals plus, for each consistency constraint, the *consequent*
//!    equality `(= v_i v_j)` — emitted by
//!    [`crate::prove_qf_bv_unsat_alethe_lowered`]. That refutation `assume`s each
//!    `(= v_i v_j)`;
//! 2. for each such consequent, an **`eq_congruent` derivation** that replaces
//!    the assume: from the argument equality `(= a b)` (an original assertion)
//!    and the abstraction's defining equations `(= v_i (f a))`, `(= v_j (f b))`,
//!    derive `(= v_i v_j)` by `eq_congruent` (giving `(= (f a) (f b))`) chained
//!    through the definitions by `eq_transitive`.
//!
//! The defining equations `(= v_i (f a_i))` are conservative fresh-variable
//! introductions (a fresh `v_i` can always be set equal to `f(a_i)`), assumed
//! explicitly as checkable hypotheses — the *trusted* step was the consistency
//! constraint, and that is now proven. The whole composes to an Alethe
//! refutation of the original assertions plus the (sound) abstraction
//! definitions, closing to the empty clause `(cl)`.
//!
//! Emission is **self-validating**: the assembled proof is run through
//! [`axeyum_cnf::check_alethe`] before return, so a returned certificate is
//! always checkable; the external Carcara binary is the trust anchor.

use std::collections::{BTreeMap, BTreeSet};

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe};
use axeyum_ir::{FuncId, SymbolId, TermArena, TermId, TermNode};

/// One functional-consistency constraint whose consequent `(= v_i v_j)` the
/// reduced refutation assumes, with the data to derive it by `eq_congruent`.
struct CongruenceCert {
    /// The fresh abstraction symbol for application `i` (renders as `v_i`).
    fresh_i: SymbolId,
    /// The fresh abstraction symbol for application `j`.
    fresh_j: SymbolId,
    /// The (rewritten) argument terms of application `i`.
    args_i: Vec<TermId>,
    /// The (rewritten) argument terms of application `j`.
    args_j: Vec<TermId>,
    /// The uninterpreted function shared by both applications.
    func: FuncId,
}

/// Emits a complete, Carcara-checkable Alethe refutation for an `unsat`
/// `QF_UFBV` conjunction decided by the Ackermann reduction — with every
/// functional-consistency constraint **proven** by `eq_congruent` rather than
/// assumed — or [`None`] when the query has no uninterpreted functions, the
/// reduced `QF_BV` problem is outside the bit-blast-emitter fragment, or the
/// assembled proof fails self-validation.
///
/// Requires `&mut TermArena` because the Ackermann reduction interns fresh
/// abstraction symbols and the consequent equalities `(= v_i v_j)`.
///
/// The certificate is sound: the consistency constraint `(a = b) -> (v_i = v_j)`
/// is derived from the argument equality and the abstraction's defining
/// equations `(= v_i (f a))` (conservative fresh-variable introductions), so no
/// reduction step is trusted. The returned proof closes to `(cl)` and has been
/// accepted by [`axeyum_cnf::check_alethe`] before return.
///
/// Returns [`None`] when:
///
/// - the conjunction contains no uninterpreted-function applications (use
///   [`crate::prove_qf_bv_unsat_alethe`] directly);
/// - the reduced `QF_BV` conjunction (rewritten originals plus the derivable
///   consistency consequents) is outside the compound-term-predicate fragment
///   the bit-blast emitter handles, or is not genuinely `unsat`;
/// - a consistency constraint's argument equality is not directly available, so
///   its consequent cannot be derived by a single `eq_congruent`; or
/// - the assembled proof fails its own [`axeyum_cnf::check_alethe`] re-check.
///
/// # Panics
///
/// Does not panic for any input; arena access is total over well-formed terms.
#[must_use]
pub fn prove_qf_ufbv_unsat_alethe(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    let elim = axeyum_rewrite::eliminate_functions(arena, assertions).ok()?;
    if !elim.had_functions() {
        return None;
    }

    // The rewritten-only (abstraction) assertions — no consistency lemmas yet.
    let rewritten = elim.abstraction().to_vec();

    // Snapshot the applications (the arg slices borrow `arena`).
    let applies: Vec<(FuncId, Vec<TermId>, SymbolId)> = elim
        .applications()
        .into_iter()
        .map(|(func, args, fresh)| (func, args.to_vec(), fresh))
        .collect();

    // The argument equalities that the *rewritten originals* directly assert,
    // keyed by an unordered pair of term ids. Used to discharge each consistency
    // constraint's antecedent: a pair of applications whose arguments are
    // pairwise asserted-equal (or identical) has a derivable consequent.
    let asserted_eqs = collect_asserted_eqs(arena, &rewritten);
    // The undirected graph those equalities induce, so an argument equality that
    // holds by *transitive closure* (`a = b ∧ b = c ⊢ a = c`) — not only by a
    // direct assertion — can still discharge a consistency antecedent, with the
    // chain proven by `eq_transitive` in `emit_arg_units`.
    let adjacency = asserted_eq_adjacency(&asserted_eqs);

    // For every pair of same-function applications with pairwise-derivable
    // argument equalities, the consequent `(= v_i v_j)` is `eq_congruent`-derivable.
    let mut certs: Vec<CongruenceCert> = Vec::new();
    for i in 0..applies.len() {
        for j in (i + 1)..applies.len() {
            let (fi, ai, vi) = &applies[i];
            let (fj, aj, vj) = &applies[j];
            if fi != fj || ai.len() != aj.len() {
                continue;
            }
            if args_pairwise_connected(&adjacency, ai, aj) {
                certs.push(CongruenceCert {
                    fresh_i: *vi,
                    fresh_j: *vj,
                    args_i: ai.clone(),
                    args_j: aj.clone(),
                    func: *fi,
                });
            }
        }
    }
    if certs.is_empty() {
        return None;
    }

    // The reduced QF_BV problem: rewritten originals plus the consistency
    // *consequents* `(= v_i v_j)` (the antecedents are discharged by the asserted
    // argument equalities, so the unconditional consequent is sound to add).
    let mut bv_assertions = rewritten.clone();
    let mut consequent_terms: Vec<(TermId, SymbolId, SymbolId)> = Vec::new();
    for cert in &certs {
        let vi = arena.var(cert.fresh_i);
        let vj = arena.var(cert.fresh_j);
        let eq = arena.eq(vi, vj).ok()?;
        bv_assertions.push(eq);
        consequent_terms.push((eq, cert.fresh_i, cert.fresh_j));
    }

    // Bit-blast refutation of the reduced QF_BV problem (lowered first so derived
    // operators in the originals still reduce). It `assume`s each consequent.
    let bv_proof = crate::prove_qf_bv_unsat_alethe_lowered(arena, &bv_assertions)?;

    // Splice: replace each consequent's `Assume` with its `eq_congruent`
    // derivation under the same id, so the consistency constraint is proven.
    let spliced =
        splice_congruence_derivations(arena, &bv_proof, &certs, &consequent_terms, &adjacency)?;

    // Self-validate before returning.
    if matches!(check_alethe(&spliced), Ok(true)) {
        Some(spliced)
    } else {
        None
    }
}

/// Collects the directly-asserted equalities among the rewritten originals as an
/// unordered set of `{a, b}` term-id pairs (canonicalised so `(a, b)` and
/// `(b, a)` match).
fn collect_asserted_eqs(arena: &TermArena, rewritten: &[TermId]) -> BTreeSet<(TermId, TermId)> {
    let mut set = BTreeSet::new();
    for &t in rewritten {
        if let TermNode::App {
            op: axeyum_ir::Op::Eq,
            args,
        } = arena.node(t)
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

/// The undirected adjacency map induced by a set of asserted equalities: each
/// `{a, b}` becomes edges `a—b` and `b—a`. Used to test whether two argument
/// terms are connected (equal by transitive closure) and to recover the path.
fn asserted_eq_adjacency(asserted: &BTreeSet<(TermId, TermId)>) -> BTreeMap<TermId, Vec<TermId>> {
    let mut adj: BTreeMap<TermId, Vec<TermId>> = BTreeMap::new();
    for &(a, b) in asserted {
        adj.entry(a).or_default().push(b);
        adj.entry(b).or_default().push(a);
    }
    adj
}

/// Whether every positional argument pair `(a_k, b_k)` is structurally identical
/// or **connected** in the asserted-equality graph (equal by transitive closure)
/// — the antecedent of the consistency constraint is then discharged, directly or
/// through an `eq_transitive` chain emitted by [`emit_arg_units`].
fn args_pairwise_connected(
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
    a: &[TermId],
    b: &[TermId],
) -> bool {
    a.iter()
        .zip(b.iter())
        .all(|(&x, &y)| x == y || eq_path(adjacency, x, y).is_some())
}

/// The shortest path of terms `from = t0, t1, …, tn = to` such that each
/// consecutive pair `{t_i, t_{i+1}}` is an asserted equality (a BFS over the
/// asserted-equality graph), or [`None`] if `from` and `to` are not connected.
/// A returned path always has `len() >= 2` (it never returns the trivial path for
/// `from == to`; callers handle identical terms separately).
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
            // Reconstruct the path from `to` back to `from`.
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

/// Replaces each consequent `(= v_i v_j)` `Assume` in `bv_proof` with an
/// `eq_congruent` derivation of `(cl (= v_i v_j))` under the same id, so the
/// functional-consistency constraint is proven from the argument equality and
/// the abstraction's defining equations rather than assumed.
fn splice_congruence_derivations(
    arena: &TermArena,
    bv_proof: &[AletheCommand],
    certs: &[CongruenceCert],
    consequents: &[(TermId, SymbolId, SymbolId)],
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
) -> Option<Vec<AletheCommand>> {
    // Map each consequent's `(= v_i v_j)` clause key to its cert.
    let mut by_consequent: BTreeMap<String, &CongruenceCert> = BTreeMap::new();
    for ((_, fi, fj), cert) in consequents.iter().zip(certs.iter()) {
        debug_assert!(*fi == cert.fresh_i && *fj == cert.fresh_j);
        let key = consequent_clause_key(arena, cert.fresh_i, cert.fresh_j);
        by_consequent.insert(key, cert);
    }

    let mut out: Vec<AletheCommand> = Vec::with_capacity(bv_proof.len() + certs.len() * 4);
    // Fresh-id allocator for the spliced derivation steps; namespaced so it never
    // collides with the bit-blast proof's `h*`/`s*`/`t*` ids.
    let mut fresh = 0usize;
    for cmd in bv_proof {
        match cmd {
            AletheCommand::Assume { id, clause } => {
                if let Some(cert) = clause_consequent_cert(clause, &by_consequent) {
                    emit_congruence_derivation(arena, &mut out, &mut fresh, id, cert, adjacency)?;
                } else {
                    out.push(cmd.clone());
                }
            }
            step @ AletheCommand::Step { .. } => out.push(step.clone()),
        }
    }
    Some(out)
}

/// If `clause` is a single positive literal `(= v_i v_j)` matching a registered
/// consequent, returns its cert.
fn clause_consequent_cert<'a>(
    clause: &AletheClause,
    by_consequent: &BTreeMap<String, &'a CongruenceCert>,
) -> Option<&'a CongruenceCert> {
    let [lit] = clause.as_slice() else {
        return None;
    };
    if lit.negated {
        return None;
    }
    by_consequent.get(&lit.atom.key()).copied()
}

/// The `(= v_i v_j)` clause key for a consequent (the fresh symbols' names).
fn consequent_clause_key(arena: &TermArena, fi: SymbolId, fj: SymbolId) -> String {
    eq_term(sym_alethe(arena, fi), sym_alethe(arena, fj)).key()
}

/// Emits, under `assume_id`, the steps deriving `(cl (= v_i v_j))` by
/// `eq_congruent` over `f` plus `eq_transitive` through the abstraction's
/// defining equations:
///
/// ```text
/// (assume d_def_i  (= v_i (f a)))     ; abstraction definition (conservative)
/// (assume d_def_j  (= v_j (f b)))
/// (assume d_arg_k  (= a_k b_k))       ; original argument equality, per k
/// (step   d_cong   (cl (not (= a b)) (= (f a) (f b))) :rule eq_congruent)
/// (step   <assume_id> (cl (= v_i v_j)) :rule eq_transitive/resolution ...)
/// ```
///
/// The final step is given the original assume's id so every downstream premise
/// referencing the consequent resolves unchanged.
fn emit_congruence_derivation(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    cert: &CongruenceCert,
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
) -> Option<()> {
    let (fname, _params, _result) = arena.function(cert.func);
    let fname = fname.to_owned();

    let vi = sym_alethe(arena, cert.fresh_i);
    let vj = sym_alethe(arena, cert.fresh_j);

    // The application terms `(f a...)` and `(f b...)` as Alethe terms.
    let args_i_alethe: Vec<AletheTerm> = cert
        .args_i
        .iter()
        .map(|&a| term_to_alethe(arena, a))
        .collect::<Option<_>>()?;
    let args_j_alethe: Vec<AletheTerm> = cert
        .args_j
        .iter()
        .map(|&b| term_to_alethe(arena, b))
        .collect::<Option<_>>()?;
    let fa = AletheTerm::App(fname.clone(), args_i_alethe.clone());
    let fb = AletheTerm::App(fname, args_j_alethe.clone());

    // Abstraction definitions, oriented for the transitive chain
    // v_i → f(a) → f(b) → v_j: `(= v_i (f a))` and `(= (f b) v_j)`. Both are
    // conservative fresh-variable introductions (a fresh `v` set equal to the
    // application term), assumed as explicit, checkable hypotheses.
    let def_i = next_id(fresh, "defi");
    out.push(AletheCommand::Assume {
        id: def_i.clone(),
        clause: vec![pos(eq_term(vi.clone(), fa.clone()))],
    });
    let def_j = next_id(fresh, "defj");
    out.push(AletheCommand::Assume {
        id: def_j.clone(),
        clause: vec![pos(eq_term(fb.clone(), vj.clone()))],
    });

    // The per-argument equality units (asserted, reflexive for identical args, or
    // an `eq_transitive` chain when the equality holds only by transitive closure).
    let arg_eq_ids = emit_arg_units(
        arena,
        out,
        fresh,
        &args_i_alethe,
        &args_j_alethe,
        &cert.args_i,
        &cert.args_j,
        adjacency,
    )?;
    let arg_pairs: Vec<(AletheTerm, AletheTerm)> = args_i_alethe
        .iter()
        .cloned()
        .zip(args_j_alethe.iter().cloned())
        .collect();

    // eq_congruent: (cl (not (= a1 b1)) … (= (f a) (f b))), resolved against the
    // argument-equality units → (cl (= (f a) (f b))).
    let mut cong_clause: AletheClause = arg_pairs
        .iter()
        .map(|(x, y)| neg(eq_term(x.clone(), y.clone())))
        .collect();
    cong_clause.push(pos(eq_term(fa.clone(), fb.clone())));
    let cong = next_id(fresh, "eqcong");
    out.push(AletheCommand::Step {
        id: cong.clone(),
        clause: cong_clause,
        rule: "eq_congruent".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    let fa_fb = next_id(fresh, "fafb");
    let mut cong_prems: Vec<String> = vec![cong];
    cong_prems.extend(arg_eq_ids);
    out.push(AletheCommand::Step {
        id: fa_fb.clone(),
        clause: vec![pos(eq_term(fa.clone(), fb.clone()))],
        rule: "resolution".to_owned(),
        premises: cong_prems,
        args: Vec::new(),
    });

    // Chain v_i = f(a) = f(b) = v_j by a single `eq_transitive` over the two
    // abstraction definitions and the derived `(= (f a) (f b))`, oriented so each
    // link shares its middle term (accepted by both `check_alethe` and Carcara):
    //
    //   eq_transitive: (cl (not (= v_i (f a))) (not (= (f a) (f b)))
    //                      (not (= (f b) v_j)) (= v_i v_j))
    let trans = next_id(fresh, "trans");
    out.push(AletheCommand::Step {
        id: trans.clone(),
        clause: vec![
            neg(eq_term(vi.clone(), fa.clone())),
            neg(eq_term(fa, fb.clone())),
            neg(eq_term(fb, vj.clone())),
            pos(eq_term(vi.clone(), vj.clone())),
        ],
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });

    // Final resolution to (cl (= v_i v_j)), under the consequent's assume id, so
    // every downstream premise referencing the consequent resolves unchanged.
    out.push(AletheCommand::Step {
        id: assume_id.to_owned(),
        clause: vec![pos(eq_term(vi, vj))],
        rule: "resolution".to_owned(),
        premises: vec![trans, def_i, fa_fb, def_j],
        args: Vec::new(),
    });

    Some(())
}

/// A fresh, namespaced derivation-step id (`!cong_<base>_<n>`), never colliding
/// with the bit-blast proof's `h*`/`s*`/`t*`/`bb*` ids.
fn next_id(fresh: &mut usize, base: &str) -> String {
    let id = format!("!cong_{base}_{}", *fresh);
    *fresh += 1;
    id
}

/// Emits one unit equality `(cl (= a_k b_k))` per argument position, returning the
/// ids in position order (the `eq_congruent` resolution premises). Each unit is:
///
/// - an `eq_reflexive` step for an identical pair (`a_k == b_k`);
/// - a direct `assume` of the asserted argument equality (a single asserted edge);
/// - or, when the equality holds only by **transitive closure** of the asserted
///   equalities, an `eq_transitive` chain: each edge of the BFS path is `assume`d
///   (it *is* an original assertion) and chained to the derived `(= a_k b_k)`.
///
/// Returns [`None`] if a path node or a non-direct pair cannot be rendered to an
/// [`AletheTerm`] (outside the argument fragment), so the caller declines the cert
/// rather than emit an unprovable step.
#[allow(clippy::too_many_arguments)]
fn emit_arg_units(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    args_i_alethe: &[AletheTerm],
    args_j_alethe: &[AletheTerm],
    args_i: &[TermId],
    args_j: &[TermId],
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
) -> Option<Vec<String>> {
    let mut ids = Vec::with_capacity(args_i_alethe.len());
    for ((&ax, &bx), (aa, bb)) in args_i
        .iter()
        .zip(args_j.iter())
        .zip(args_i_alethe.iter().zip(args_j_alethe.iter()))
    {
        if ax == bx {
            // Identical argument: reflexive equality `(= a a)` via eq_reflexive.
            let r = next_id(fresh, "refl");
            out.push(AletheCommand::Step {
                id: r.clone(),
                clause: vec![pos(eq_term(aa.clone(), bb.clone()))],
                rule: "eq_reflexive".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
            });
            ids.push(r);
            continue;
        }
        let path = eq_path(adjacency, ax, bx)?;
        if path.len() == 2 {
            // A single asserted edge `(= a_k b_k)`: assume it directly (unchanged).
            let g = next_id(fresh, "arg");
            out.push(AletheCommand::Assume {
                id: g.clone(),
                clause: vec![pos(eq_term(aa.clone(), bb.clone()))],
            });
            ids.push(g);
        } else {
            // Transitive closure `a_k = m_1 = … = b_k`: assume each edge and chain
            // them with one `eq_transitive` step (shared middle terms) resolved to
            // `(= a_k b_k)`.
            let nodes: Vec<AletheTerm> = path
                .iter()
                .map(|&n| term_to_alethe(arena, n))
                .collect::<Option<_>>()?;
            // Assume every edge `(= n_i n_{i+1})` — each is an original assertion.
            let mut edge_ids = Vec::with_capacity(nodes.len() - 1);
            for w in nodes.windows(2) {
                let e = next_id(fresh, "edge");
                out.push(AletheCommand::Assume {
                    id: e.clone(),
                    clause: vec![pos(eq_term(w[0].clone(), w[1].clone()))],
                });
                edge_ids.push(e);
            }
            // eq_transitive tautology: (cl (not (= n0 n1)) … (not (= n_{m-1} nm)) (= n0 nm)).
            let mut trans_clause: AletheClause = nodes
                .windows(2)
                .map(|w| neg(eq_term(w[0].clone(), w[1].clone())))
                .collect();
            trans_clause.push(pos(eq_term(aa.clone(), bb.clone())));
            let trans = next_id(fresh, "argtrans");
            out.push(AletheCommand::Step {
                id: trans.clone(),
                clause: trans_clause,
                rule: "eq_transitive".to_owned(),
                premises: Vec::new(),
                args: Vec::new(),
            });
            // Resolve the tautology against the edge units → (cl (= a_k b_k)).
            let derived = next_id(fresh, "argeq");
            let mut prems = vec![trans];
            prems.extend(edge_ids);
            out.push(AletheCommand::Step {
                id: derived.clone(),
                clause: vec![pos(eq_term(aa.clone(), bb.clone()))],
                rule: "resolution".to_owned(),
                premises: prems,
                args: Vec::new(),
            });
            ids.push(derived);
        }
    }
    Some(ids)
}

/// A symbol rendered as an Alethe `Const` of its declared name.
fn sym_alethe(arena: &TermArena, sym: SymbolId) -> AletheTerm {
    let (name, _sort) = arena.symbol(sym);
    AletheTerm::Const(name.to_owned())
}

/// Converts an IR term to an [`AletheTerm`] for the argument fragment (symbols,
/// bit-vector constants, and uninterpreted applications), or [`None`] otherwise.
fn term_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(bv_const_literal(*width, *value)))
        }
        TermNode::App {
            op: axeyum_ir::Op::Apply(func),
            args,
        } => {
            let (name, _params, _result) = arena.function(*func);
            let name = name.to_owned();
            let converted = args
                .iter()
                .map(|&a| term_to_alethe(arena, a))
                .collect::<Option<Vec<_>>>()?;
            Some(AletheTerm::App(name, converted))
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
