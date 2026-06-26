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

use std::collections::{BTreeMap, BTreeSet, HashMap};

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe};
use axeyum_egraph::{EGraph, ENodeId, ProofStep};
use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};

/// One functional-consistency constraint whose consequent `(= v_i v_j)` the
/// reduced refutation assumes, with the data to derive it by `eq_congruent`.
///
/// Shared with the arithmetic-residual emitter `crate::qfuflia_alethe`
/// (`QF_UFLIA`/`QF_UFLRA`), which builds the same Ackermann congruence units but
/// hands the residual to the `lia_generic`/`la_generic` arithmetic emitters
/// instead of the bit-blast emitter.
pub(crate) struct CongruenceCert {
    /// The fresh abstraction symbol for application `i` (renders as `v_i`).
    pub(crate) fresh_i: SymbolId,
    /// The fresh abstraction symbol for application `j`.
    pub(crate) fresh_j: SymbolId,
    /// The (rewritten) argument terms of application `i`.
    pub(crate) args_i: Vec<TermId>,
    /// The (rewritten) argument terms of application `j`.
    pub(crate) args_j: Vec<TermId>,
    /// The uninterpreted function shared by both applications.
    pub(crate) func: FuncId,
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
    let congruence = build_ackermann_congruence(arena, assertions)?;

    // The reduced QF_BV problem: rewritten originals plus the consistency
    // *consequents* `(= v_i v_j)` (the antecedents are discharged by the asserted
    // argument equalities, so the unconditional consequent is sound to add).
    let bv_assertions = congruence.reduced_assertions();

    // Bit-blast refutation of the reduced QF_BV problem (lowered first so derived
    // operators in the originals still reduce). It `assume`s each consequent.
    let bv_proof = crate::prove_qf_bv_unsat_alethe_lowered(arena, &bv_assertions)?;

    // Splice: replace each consequent's `Assume` with its `eq_congruent`
    // derivation under the same id, so the consistency constraint is proven.
    let spliced = congruence.splice(arena, &bv_proof)?;

    // Self-validate before returning.
    if matches!(check_alethe(&spliced), Ok(true)) {
        Some(spliced)
    } else {
        None
    }
}

/// The reusable Ackermann-congruence building blocks for a `QF_UF*` refutation:
/// the rewritten-only (abstraction) assertions, the derivable functional-
/// consistency consequents `(= v_i v_j)`, and the asserted-equality / congruence-
/// closure structures used to *prove* each consequent by `eq_congruent`.
///
/// Both the bit-blast emitter ([`prove_qf_ufbv_unsat_alethe`]) and the arithmetic
/// emitter (`crate::qfuflia_alethe`, `QF_UFLIA`/`QF_UFLRA`) share this prefix and
/// differ only in which residual emitter refutes the reduced (Ackermannized)
/// problem and which checker re-validates the spliced proof — so the otherwise-
/// *trusted* functional-consistency reduction is proven identically on both paths.
pub(crate) struct AckermannCongruence {
    /// The rewritten-only assertions (each UF application abstracted to a fresh
    /// same-sorted constant), before the consistency consequents are appended.
    rewritten: Vec<TermId>,
    /// The functional-consistency certificates whose consequents are derivable.
    certs: Vec<CongruenceCert>,
    /// Per consequent, its interned `(= v_i v_j)` term and the two fresh symbols.
    consequent_terms: Vec<(TermId, SymbolId, SymbolId)>,
    /// The asserted-equality adjacency graph (transitive closure of argument eqs).
    adjacency: BTreeMap<TermId, Vec<TermId>>,
    /// The congruence-closure bridge (the e-graph fallback), if it built.
    cong: Option<CongBridge>,
}

impl AckermannCongruence {
    /// The rewritten originals after Ackermann abstraction, before consistency
    /// consequents are appended.
    pub(crate) fn rewritten_assertions(&self) -> &[TermId] {
        &self.rewritten
    }

    /// The derivable functional-consistency consequents `(= v_i v_j)`.
    pub(crate) fn consequent_assertions(&self) -> impl Iterator<Item = TermId> + '_ {
        self.consequent_terms.iter().map(|&(eq, _, _)| eq)
    }

    /// The reduced (Ackermannized) assertions: the rewritten originals plus each
    /// derivable consistency *consequent* `(= v_i v_j)`. For a `QF_UFLIA`/
    /// `QF_UFLRA` query whose only UF applications are arithmetic-sorted, this is a
    /// pure linear-integer/real conjunction the arithmetic emitter can refute.
    pub(crate) fn reduced_assertions(&self) -> Vec<TermId> {
        let mut out = self.rewritten.clone();
        out.extend(self.consequent_terms.iter().map(|&(eq, _, _)| eq));
        out
    }

    /// Splices each consequent's `Assume` in `residual_proof` with its
    /// `eq_congruent` derivation under the same id (so the consistency constraint
    /// is proven, not assumed), returning the assembled proof. The residual proof
    /// may be a bit-blast refutation or an `lia_generic`/`la_generic` refutation;
    /// the splice only rewrites the consequent assumes, leaving the rest intact.
    pub(crate) fn splice(
        &self,
        arena: &TermArena,
        residual_proof: &[AletheCommand],
    ) -> Option<Vec<AletheCommand>> {
        splice_congruence_derivations(
            arena,
            residual_proof,
            &self.certs,
            &self.consequent_terms,
            &self.adjacency,
            self.cong.as_ref(),
        )
    }
}

/// Builds the [`AckermannCongruence`] prefix shared by the `QF_UFBV` and
/// `QF_UFLIA`/`QF_UFLRA` emitters: Ackermann-abstracts every UF application to a
/// fresh same-sorted constant, collects the derivable functional-consistency
/// consequents, and interns each consequent equality `(= v_i v_j)`. Returns
/// [`None`] when the query has no uninterpreted functions or no consequent is
/// derivable (the antecedent of every consistency constraint fails to discharge),
/// so the caller declines the cert.
pub(crate) fn build_ackermann_congruence(
    arena: &mut TermArena,
    assertions: &[TermId],
) -> Option<AckermannCongruence> {
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

    // Each application's defining equation `v_i = f(args_i)` as
    // `(fresh var term, func, rewritten args)`, interned here while `arena` is
    // mutable (the e-graph fallback needs the fresh-symbol var term immutably).
    let definitions: Vec<(TermId, FuncId, Vec<TermId>)> = applies
        .iter()
        .map(|(func, args, fresh)| (arena.var(*fresh), *func, args.clone()))
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

    // The congruence-closure over the asserted equalities *and* the abstraction's
    // defining equations `v_i = f(args_i)`, used as a fallback when an argument
    // pair is equal by *congruence* (e.g. the two `f`-applications of `f(g(a))` and
    // `f(g(b))` have arguments `v0 = g(a)` and `v1 = g(b)`, equal because `a = b`)
    // rather than by a transitive chain of asserted edges. Built once here and
    // threaded through the emitter; `emit_arg_units` consults it only when the
    // asserted-edge BFS declines. `None` (build failure) simply disables the
    // fallback. The defining equations it assumes are the same conservative
    // fresh-variable introductions the rest of the cert assumes, present in the
    // matching problem as `(= !fn_app_i (f a_i))` assertions.
    let cong = CongBridge::build(arena, &asserted_eqs, &definitions);

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
            if args_pairwise_connected(&adjacency, cong.as_ref(), ai, aj) {
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

    // Intern each consistency *consequent* `(= v_i v_j)` (the antecedents are
    // discharged by the asserted argument equalities, so the unconditional
    // consequent is sound to add to the residual problem).
    let mut consequent_terms: Vec<(TermId, SymbolId, SymbolId)> = Vec::new();
    for cert in &certs {
        let vi = arena.var(cert.fresh_i);
        let vj = arena.var(cert.fresh_j);
        let eq = arena.eq(vi, vj).ok()?;
        consequent_terms.push((eq, cert.fresh_i, cert.fresh_j));
    }

    Some(AckermannCongruence {
        rewritten,
        certs,
        consequent_terms,
        adjacency,
        cong,
    })
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

/// Whether every positional argument pair `(a_k, b_k)` is structurally identical,
/// **connected** in the asserted-equality graph (equal by transitive closure), or
/// equal by **congruence closure** of the asserted equalities (the e-graph
/// fallback) — the antecedent of the consistency constraint is then discharged,
/// directly, through an `eq_transitive` chain, or through an `eq_congruent`
/// derivation emitted by [`emit_arg_units`].
fn args_pairwise_connected(
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
    cong: Option<&CongBridge>,
    a: &[TermId],
    b: &[TermId],
) -> bool {
    a.iter().zip(b.iter()).all(|(&x, &y)| {
        x == y || eq_path(adjacency, x, y).is_some() || cong.is_some_and(|c| c.terms_equal(x, y))
    })
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
    cong: Option<&CongBridge>,
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
                    emit_congruence_derivation(
                        arena, &mut out, &mut fresh, id, cert, adjacency, cong,
                    )?;
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
#[allow(clippy::too_many_arguments)]
fn emit_congruence_derivation(
    arena: &TermArena,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    assume_id: &str,
    cert: &CongruenceCert,
    adjacency: &BTreeMap<TermId, Vec<TermId>>,
    cong: Option<&CongBridge>,
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
        cong,
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
/// - when the equality holds only by **transitive closure** of the asserted
///   equalities, an `eq_transitive` chain: each edge of the BFS path is `assume`d
///   (it *is* an original assertion) and chained to the derived `(= a_k b_k)`;
/// - or, when neither identical nor connected through *asserted* edges but the
///   argument pair is equal by **congruence closure** of the asserted equalities
///   (e.g. `g(a) = g(b)` because `a = b`), an e-graph-driven derivation (`eq_input`
///   assumes, `eq_congruent` over recursively-derived argument equalities, threaded
///   through `eq_transitive`) supplied by [`CongBridge`].
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
    cong: Option<&CongBridge>,
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
        let Some(path) = eq_path(adjacency, ax, bx) else {
            // No chain of *asserted* edges connects the pair. Fall back to the
            // congruence closure of the asserted equalities via the e-graph: if it
            // makes `a_k` and `b_k` equal (e.g. through `g(a) = g(b)` from `a = b`),
            // emit the e-graph-driven derivation, returning its unit's id. If the
            // e-graph also cannot connect them, this declines (the pair is genuinely
            // not entailed) and the whole cert is declined.
            let bridge = cong?;
            let derived = emit_congruence_arg_unit(arena, bridge, out, fresh, ax, bx)?;
            ids.push(derived);
            continue;
        };
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

// --- Congruence-closure fallback ---------------------------------------------
//
// When an argument pair `(a_k, b_k)` is equal not through a chain of *asserted*
// equality edges but through the **congruence closure** of the asserted
// equalities (e.g. `g(a) = g(b)` because `a = b`), the asserted-edge BFS
// (`eq_path`) declines. [`CongBridge`] builds an e-graph over the rewritten
// assertions (every term added before any merge, so congruent applications stay
// distinct and their congruence edge is recorded) and walks
// [`EGraph::explain_steps`] to emit a checkable `(= a_k b_k)` derivation — the
// same explain→Alethe conversion the EUF emitter uses, specialised to the
// argument fragment. A bad or absent derivation simply yields `None`, so the
// self-validated emitter declines rather than emit an unprovable step.

/// What a `decl` identifies in the term→e-graph bridge.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DeclKey {
    Symbol(usize),
    Func(usize),
    Op(String),
    Const(String),
}

/// Why two e-nodes were merged, with the data to render the equality as an Alethe
/// `assume` clause when an [`ProofStep::Input`] walks that merge.
enum CongReason {
    /// An asserted equality `(= a b)` (an original problem premise).
    Asserted(TermId, TermId),
    /// An abstraction defining equation `(= fresh (func rewritten_args))` — a
    /// conservative fresh-variable introduction, present in the matching problem.
    /// `fresh_var` is the interned variable term for the fresh symbol.
    Definition {
        fresh_var: TermId,
        func: FuncId,
        args: Vec<TermId>,
    },
}

/// An e-graph over the rewritten assertions whose merges are the asserted
/// equalities *and* the abstraction defining equations, plus a term↔node bridge so
/// [`EGraph::explain_steps`] can be converted back to Alethe terms. Used to
/// discharge argument equalities that hold only by congruence closure.
struct CongBridge {
    egraph: EGraph,
    node_to_term: HashMap<ENodeId, TermId>,
    term_to_node: HashMap<TermId, ENodeId>,
    /// Alethe rendering for synthetic e-nodes (application nodes built directly in
    /// the e-graph, with no backing interned [`TermId`]).
    synthetic_alethe: HashMap<ENodeId, AletheTerm>,
    /// Per merge reason index: how the merge was justified.
    merges: Vec<CongReason>,
}

impl CongBridge {
    /// Builds the e-graph over the asserted equalities and the abstraction defining
    /// equations `v_i = f(args_i)`. Every term is added **before** any merge, so
    /// congruent applications like `g(a)` and `g(b)` exist as distinct nodes and the
    /// proof forest records the congruence edge. Returns [`None`] if a side falls
    /// outside the renderable fragment (then the fallback is simply disabled).
    fn build(
        arena: &TermArena,
        asserted: &BTreeSet<(TermId, TermId)>,
        definitions: &[(TermId, FuncId, Vec<TermId>)],
    ) -> Option<Self> {
        let mut bridge = CongBridge {
            egraph: EGraph::new(),
            node_to_term: HashMap::new(),
            term_to_node: HashMap::new(),
            synthetic_alethe: HashMap::new(),
            merges: Vec::new(),
        };
        let mut decls: HashMap<DeclKey, u32> = HashMap::new();
        let mut next_decl = 0u32;

        // Add every term (and the synthetic application nodes) first, so congruence
        // edges survive. Asserted-equality endpoints…
        let mut asserted_nodes: Vec<(ENodeId, ENodeId)> = Vec::with_capacity(asserted.len());
        for &(a, b) in asserted {
            let na = bridge.add_term(arena, a, &mut decls, &mut next_decl)?;
            let nb = bridge.add_term(arena, b, &mut decls, &mut next_decl)?;
            asserted_nodes.push((na, nb));
        }
        // …and, per application, the fresh symbol node and the application node
        // `(func rewritten_args)` over the rewritten argument nodes. The application
        // node is built directly in the e-graph (it need not be an interned term).
        let mut def_nodes: Vec<(ENodeId, ENodeId)> = Vec::with_capacity(definitions.len());
        for (fresh_var, func, args) in definitions {
            let fresh_node = bridge.add_term(arena, *fresh_var, &mut decls, &mut next_decl)?;
            let mut child_nodes = Vec::with_capacity(args.len());
            let mut arg_alethe = Vec::with_capacity(args.len());
            for &arg in args {
                child_nodes.push(bridge.add_term(arena, arg, &mut decls, &mut next_decl)?);
                arg_alethe.push(term_to_alethe(arena, arg)?);
            }
            let decl = decl_id(&mut decls, &mut next_decl, DeclKey::Func(func.index()));
            let app_node = bridge.egraph.add(decl, &child_nodes);
            let (fname, _params, _result) = arena.function(*func);
            bridge
                .synthetic_alethe
                .entry(app_node)
                .or_insert_with(|| AletheTerm::App(fname.to_owned(), arg_alethe));
            def_nodes.push((fresh_node, app_node));
        }

        // Then merge. Asserted equalities…
        for (&(na, nb), &(a, b)) in asserted_nodes.iter().zip(asserted.iter()) {
            let reason = u32::try_from(bridge.merges.len()).ok()?;
            bridge.egraph.merge(na, nb, reason);
            bridge.merges.push(CongReason::Asserted(a, b));
        }
        // …and the defining equations.
        for (&(fresh_node, app_node), (fresh_var, func, args)) in
            def_nodes.iter().zip(definitions.iter())
        {
            let reason = u32::try_from(bridge.merges.len()).ok()?;
            bridge.egraph.merge(fresh_node, app_node, reason);
            bridge.merges.push(CongReason::Definition {
                fresh_var: *fresh_var,
                func: *func,
                args: args.clone(),
            });
        }
        Some(bridge)
    }

    /// The e-node for `term`, creating it (and its subterms) on first use; [`None`]
    /// for a shape outside the renderable fragment.
    fn add_term(
        &mut self,
        arena: &TermArena,
        term: TermId,
        decls: &mut HashMap<DeclKey, u32>,
        next_decl: &mut u32,
    ) -> Option<ENodeId> {
        if let Some(&n) = self.term_to_node.get(&term) {
            return Some(n);
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = decl_id(decls, next_decl, DeclKey::Symbol(s.index()));
                self.egraph.add(decl, &[])
            }
            TermNode::BvConst { .. } => {
                let key = DeclKey::Const(format!("{:?}", arena.node(term)));
                let decl = decl_id(decls, next_decl, key);
                self.egraph.add(decl, &[])
            }
            TermNode::App { op, args } => {
                let op = *op;
                let args = args.clone();
                let mut child_nodes = Vec::with_capacity(args.len());
                for &a in &args {
                    child_nodes.push(self.add_term(arena, a, decls, next_decl)?);
                }
                let key = match op {
                    Op::Apply(func) => DeclKey::Func(func.index()),
                    other => DeclKey::Op(format!("{other:?}")),
                };
                let decl = decl_id(decls, next_decl, key);
                self.egraph.add(decl, &child_nodes)
            }
            _ => return None,
        };
        self.term_to_node.insert(term, node);
        self.node_to_term.entry(node).or_insert(term);
        Some(node)
    }

    /// Whether `a` and `b` are equal in the congruence closure (both must be known
    /// terms in the bridge).
    fn terms_equal(&self, a: TermId, b: TermId) -> bool {
        match (self.term_to_node.get(&a), self.term_to_node.get(&b)) {
            (Some(&na), Some(&nb)) => self.egraph.equal(na, nb),
            _ => false,
        }
    }

    /// The Alethe term for e-node `n`: a synthetic application node's stored
    /// rendering, or the first interned term recorded for it.
    fn node_alethe(&self, arena: &TermArena, n: ENodeId) -> Option<AletheTerm> {
        if let Some(t) = self.synthetic_alethe.get(&n) {
            return Some(t.clone());
        }
        let term = *self.node_to_term.get(&n)?;
        term_to_alethe(arena, term)
    }
}

/// A stable `decl` id for `key`.
fn decl_id(decls: &mut HashMap<DeclKey, u32>, next: &mut u32, key: DeclKey) -> u32 {
    if let Some(&d) = decls.get(&key) {
        return d;
    }
    let d = *next;
    *next += 1;
    decls.insert(key, d);
    d
}

/// Emits the e-graph-driven derivation of `(cl (= a_k b_k))` for an argument pair
/// equal by congruence closure, returning the id of the unit naming that equality.
/// [`None`] if the e-graph does not connect the pair or a node fails to render.
fn emit_congruence_arg_unit(
    arena: &TermArena,
    bridge: &CongBridge,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    ax: TermId,
    bx: TermId,
) -> Option<String> {
    let na = *bridge.term_to_node.get(&ax)?;
    let nb = *bridge.term_to_node.get(&bx)?;
    if !bridge.egraph.equal(na, nb) {
        return None;
    }
    derive_eq_via_steps(arena, bridge, out, fresh, na, nb)
}

/// Emits the steps deriving `(cl (= term(na) term(nb)))` by walking
/// [`EGraph::explain_steps`]`(na, nb)`, returning the id of the unit naming that
/// equality. Mirrors the EUF emitter's recursion, specialised to the `!cong_*` id
/// namespace and the argument fragment.
///
/// - `na == nb`: `eq_reflexive` `(cl (= t t))`.
/// - otherwise: each proof step is an oriented unit `(cl (= x y))` walking
///   `na → nb` — an [`ProofStep::Input`] is the asserted equality (flipped with
///   `eq_symmetric` when the path runs the other way); a [`ProofStep::Congruence`]
///   is an `eq_congruent` over its recursively-derived argument units. A single
///   step is returned directly; multiple steps thread through one `eq_transitive`.
fn derive_eq_via_steps(
    arena: &TermArena,
    bridge: &CongBridge,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    na: ENodeId,
    nb: ENodeId,
) -> Option<String> {
    if na == nb {
        let a = bridge.node_alethe(arena, na)?;
        let r = next_id(fresh, "refl");
        out.push(AletheCommand::Step {
            id: r.clone(),
            clause: vec![pos(eq_term(a.clone(), a))],
            rule: "eq_reflexive".to_owned(),
            premises: Vec::new(),
            args: Vec::new(),
        });
        return Some(r);
    }

    let steps = bridge.egraph.explain_steps(na, nb);
    if steps.is_empty() {
        return None;
    }

    // Order the steps into a single `na → nb` chain by greedily following the step
    // incident to the current node, orienting each step's unit accordingly.
    let mut remaining: Vec<&ProofStep> = steps.iter().collect();
    let mut cur = na;
    let mut links: Vec<CongLink> = Vec::with_capacity(steps.len());
    while !remaining.is_empty() {
        let pos_idx = remaining.iter().position(|s| {
            let (sa, sb) = step_endpoints(s);
            sa == cur || sb == cur
        })?;
        let step = remaining.remove(pos_idx);
        let (sa, sb) = step_endpoints(step);
        let (from, to) = if sa == cur { (sa, sb) } else { (sb, sa) };
        let from_alethe = bridge.node_alethe(arena, from)?;
        let to_alethe = bridge.node_alethe(arena, to)?;
        let unit_id = emit_step_unit(
            arena,
            bridge,
            out,
            fresh,
            step,
            from,
            to,
            &from_alethe,
            &to_alethe,
        )?;
        links.push(CongLink {
            id: unit_id,
            lhs: from_alethe,
            rhs: to_alethe,
        });
        cur = to;
    }

    if let [only] = links.as_slice() {
        return Some(only.id.clone());
    }
    chain_transitive(out, fresh, &links)
}

/// One oriented equality link `(= lhs rhs)` along a derivation chain.
struct CongLink {
    id: String,
    lhs: AletheTerm,
    rhs: AletheTerm,
}

/// Endpoints `(a, b)` of a proof step.
fn step_endpoints(step: &ProofStep) -> (ENodeId, ENodeId) {
    match step {
        ProofStep::Input { a, b, .. } | ProofStep::Congruence { a, b, .. } => (*a, *b),
    }
}

/// Emits the oriented unit `(cl (= term(from) term(to)))` for one proof step.
#[allow(clippy::too_many_arguments)]
fn emit_step_unit(
    arena: &TermArena,
    bridge: &CongBridge,
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    step: &ProofStep,
    from: ENodeId,
    to: ENodeId,
    from_alethe: &AletheTerm,
    to_alethe: &AletheTerm,
) -> Option<String> {
    match step {
        ProofStep::Input { a, reason, .. } => {
            // The merge `merges[reason]`: either an asserted equality `(= ea eb)` or
            // an abstraction defining equation `(= fresh (func args))`. Render its
            // oriented sides and the e-node its `lhs` term maps to, to decide whether
            // the stored orientation matches the `from → to` path direction.
            let reason = bridge.merges.get(*reason as usize)?;
            let (lhs, rhs, lhs_node) = match reason {
                CongReason::Asserted(ea, eb) => {
                    let lhs = term_to_alethe(arena, *ea)?;
                    let rhs = term_to_alethe(arena, *eb)?;
                    let lhs_node = bridge.term_to_node.get(ea).copied();
                    (lhs, rhs, lhs_node)
                }
                CongReason::Definition {
                    fresh_var,
                    func,
                    args,
                } => {
                    // `(= fresh (func args))` — fresh symbol on the left.
                    let lhs = term_to_alethe(arena, *fresh_var)?;
                    let arg_alethe: Vec<AletheTerm> = args
                        .iter()
                        .map(|&arg| term_to_alethe(arena, arg))
                        .collect::<Option<_>>()?;
                    let (fname, _params, _result) = arena.function(*func);
                    let rhs = AletheTerm::App(fname.to_owned(), arg_alethe);
                    let lhs_node = bridge.term_to_node.get(fresh_var).copied();
                    (lhs, rhs, lhs_node)
                }
            };
            let assume_id = next_id(fresh, "arg");
            out.push(AletheCommand::Assume {
                id: assume_id.clone(),
                clause: vec![pos(eq_term(lhs.clone(), rhs.clone()))],
            });
            // The assume orients `lhs → rhs`. The step's first endpoint `a` is the
            // e-node of one side; if `lhs`'s node is the path's `from`, the
            // orientation already matches, else flip via `eq_symmetric`.
            let _ = a;
            let stored_forward = lhs_node == Some(from);
            if stored_forward {
                Some(assume_id)
            } else {
                Some(flip_unit(
                    out,
                    fresh,
                    &assume_id,
                    &lhs,
                    &rhs,
                    from_alethe,
                    to_alethe,
                ))
            }
        }
        ProofStep::Congruence { args, .. } => {
            let from_args = bridge.egraph.args(from).to_vec();
            let to_args = bridge.egraph.args(to).to_vec();
            if from_args.len() != to_args.len() || from_args.len() != args.len() {
                return None;
            }
            let mut arg_units: Vec<String> = Vec::with_capacity(from_args.len());
            let mut arg_pairs: Vec<(AletheTerm, AletheTerm)> = Vec::with_capacity(from_args.len());
            for (&xa, &xb) in from_args.iter().zip(to_args.iter()) {
                let unit_id = derive_eq_via_steps(arena, bridge, out, fresh, xa, xb)?;
                let lhs = bridge.node_alethe(arena, xa)?;
                let rhs = bridge.node_alethe(arena, xb)?;
                arg_units.push(unit_id);
                arg_pairs.push((lhs, rhs));
            }
            Some(emit_congruence_step(
                out,
                fresh,
                &arg_units,
                &arg_pairs,
                from_alethe,
                to_alethe,
            ))
        }
    }
}

/// Flips a unit `(cl (= ea eb))` into `(cl (= from to))` (where `(from, to)` is
/// `(eb, ea)`) via the `symm` rule (premise the unit, single-term conclusion).
/// Returns the flipped unit's id. `ea`/`eb` are unused for the conclusion (which is
/// stated as `(= from to)`) but kept for documentation symmetry with the caller.
fn flip_unit(
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    unit_id: &str,
    _ea: &AletheTerm,
    _eb: &AletheTerm,
    from: &AletheTerm,
    to: &AletheTerm,
) -> String {
    // symm: from premise `(= ea eb)` derive `(cl (= eb ea))` = `(cl (= from to))`.
    let flipped = next_id(fresh, "flip");
    out.push(AletheCommand::Step {
        id: flipped.clone(),
        clause: vec![pos(eq_term(from.clone(), to.clone()))],
        rule: "symm".to_owned(),
        premises: vec![unit_id.to_owned()],
        args: Vec::new(),
    });
    flipped
}

/// Emits `eq_congruent` over the argument units plus a resolution, deriving
/// `(cl (= from to))`. Returns the resolution step's id.
fn emit_congruence_step(
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    arg_units: &[String],
    arg_pairs: &[(AletheTerm, AletheTerm)],
    from: &AletheTerm,
    to: &AletheTerm,
) -> String {
    let mut cong_clause: AletheClause = arg_pairs
        .iter()
        .map(|(x, y)| neg(eq_term(x.clone(), y.clone())))
        .collect();
    cong_clause.push(pos(eq_term(from.clone(), to.clone())));
    let cong = next_id(fresh, "eqcong");
    out.push(AletheCommand::Step {
        id: cong.clone(),
        clause: cong_clause,
        rule: "eq_congruent".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    let derived = next_id(fresh, "congeq");
    let mut prems = vec![cong];
    prems.extend(arg_units.iter().cloned());
    out.push(AletheCommand::Step {
        id: derived.clone(),
        clause: vec![pos(eq_term(from.clone(), to.clone()))],
        rule: "resolution".to_owned(),
        premises: prems,
        args: Vec::new(),
    });
    derived
}

/// Threads the oriented links left-to-right through one `eq_transitive` plus a
/// resolution, deriving `(cl (= lhs(first) rhs(last)))`. Assumes `links.len() >= 2`.
fn chain_transitive(
    out: &mut Vec<AletheCommand>,
    fresh: &mut usize,
    links: &[CongLink],
) -> Option<String> {
    let a_first = links.first()?.lhs.clone();
    let b_last = links.last()?.rhs.clone();

    let mut trans_clause: AletheClause = links
        .iter()
        .map(|l| neg(eq_term(l.lhs.clone(), l.rhs.clone())))
        .collect();
    trans_clause.push(pos(eq_term(a_first.clone(), b_last.clone())));
    let trans = next_id(fresh, "argtrans");
    out.push(AletheCommand::Step {
        id: trans.clone(),
        clause: trans_clause,
        rule: "eq_transitive".to_owned(),
        premises: Vec::new(),
        args: Vec::new(),
    });
    let derived = next_id(fresh, "argeq");
    let mut prems = vec![trans];
    prems.extend(links.iter().map(|l| l.id.clone()));
    out.push(AletheCommand::Step {
        id: derived.clone(),
        clause: vec![pos(eq_term(a_first, b_last))],
        rule: "resolution".to_owned(),
        premises: prems,
        args: Vec::new(),
    });
    Some(derived)
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
