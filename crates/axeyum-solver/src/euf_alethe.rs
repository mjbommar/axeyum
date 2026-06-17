//! Alethe proof **emission** for transitivity-based EUF refutations (Track 3,
//! the producer counterpart to [`axeyum_cnf::check_alethe`]).
//!
//! The solver already *checks* Alethe proofs; this module *emits* one for a
//! class of EUF conflicts — a transitivity chain over equality atoms refuting a
//! disequality. Emission is **self-validating**: every proof this builds is run
//! through [`axeyum_cnf::check_alethe`] before being returned, so a buggy build
//! is *rejected* (returns `None`), never returned wrong. The acceptance test is
//! therefore the correctness gate: a returned proof has been independently
//! re-checked and derives the empty clause `(cl)`.
//!
//! The conflict core comes from [`crate::prove_unsat_by_congruence`] — a subset
//! of the original assertions that is UNSAT by congruence. For the slice handled
//! here that core is a set of equality terms `(= a b)` plus exactly one
//! disequality term `(not (= s t))`. We BFS a path `s = p0, p1, …, pk = t`
//! through the equality edges, emit oriented unit clauses for each link (with an
//! `eq_symmetric` rewrite when an edge is stored reversed), an `eq_transitive`
//! step over the chain, resolve to `(= s t)`, and resolve that against the
//! disequality assume to reach `(cl)`.

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// Emits a checkable Alethe refutation for a transitivity-based EUF conflict in
/// `assertions`, or `None` if the query is not refuted by congruence or the
/// conflict is not a pure transitivity chain this slice handles.
///
/// The returned proof, when non-`None`, is guaranteed to pass
/// [`axeyum_cnf::check_alethe`] (it is self-validated before return) and to
/// derive the empty clause `(cl)`. `None` is returned when:
///
/// - [`crate::prove_unsat_by_congruence`] does not refute the assertions;
/// - the conflict core is not exactly some equality terms `(= a b)` plus one
///   disequality `(not (= s t))`;
/// - no equality path connects the disequality's two sides;
/// - a core term references an operator or constant the term→Alethe converter
///   does not cover; or
/// - the assembled proof fails its own [`axeyum_cnf::check_alethe`] re-check.
///
/// The proof is deterministic: assume ids are `h0, h1, …` and step ids are
/// `s0, s1, …` in emission order, and the term converter assigns stable names.
#[must_use]
pub fn prove_qf_uf_unsat_alethe(
    arena: &TermArena,
    assertions: &[TermId],
) -> Option<Vec<AletheCommand>> {
    let conflict = crate::prove_unsat_by_congruence(arena, assertions)?;

    // Classify the core into equality edges and exactly one disequality.
    let mut edges: Vec<(TermId, TermId)> = Vec::new();
    let mut diseq: Option<(TermId, TermId)> = None;
    for &term in &conflict.core {
        match classify(arena, term)? {
            CoreAtom::Eq(a, b) => edges.push((a, b)),
            CoreAtom::Diseq(s, t) => {
                if diseq.is_some() {
                    return None; // more than one disequality: outside this slice
                }
                diseq = Some((s, t));
            }
        }
    }
    let (s, t) = diseq?;

    // BFS an equality path from `s` to `t` over the undirected equality graph.
    let path = bfs_path(s, t, &edges)?;
    if path.len() < 2 {
        // s == t with no link; a `(not (= s s))` core is degenerate — skip.
        return None;
    }

    let mut builder = Builder::new();

    // For each consecutive pair, emit an oriented unit clause `(cl (= p_i p_{i+1}))`
    // and record its id plus the equality term.
    let mut oriented: Vec<(String, AletheTerm, AletheTerm)> = Vec::new();
    for window in path.windows(2) {
        let (pi, pj) = (window[0], window[1]);
        if pi == pj {
            continue; // no edge needed
        }
        let lhs = term_to_alethe(arena, pi)?;
        let rhs = term_to_alethe(arena, pj)?;
        let id = builder.oriented_unit(&edges, pi, pj, &lhs, &rhs)?;
        oriented.push((id, lhs, rhs));
    }
    if oriented.is_empty() {
        return None;
    }

    // eq_transitive: (cl (not (= p0 p1)) … (not (= p_{k-1} pk)) (= p0 pk)).
    let s_alethe = oriented.first().map(|(_, a, _)| a.clone())?;
    let t_alethe = oriented.last().map(|(_, _, b)| b.clone())?;
    let mut trans_clause: AletheClause = oriented
        .iter()
        .map(|(_, a, b)| AletheLit {
            atom: eq_term(a.clone(), b.clone()),
            negated: true,
        })
        .collect();
    trans_clause.push(AletheLit {
        atom: eq_term(s_alethe.clone(), t_alethe.clone()),
        negated: false,
    });
    let trans_id = builder.step(trans_clause, "eq_transitive", &[]);

    // Resolve the eq_transitive clause against each oriented unit to derive (= s t).
    // The running clause starts as the eq_transitive clause; resolving link `k` (in
    // order) removes its negated literal, leaving the still-unresolved links
    // [k+1..] plus the positive (= s t) conclusion.
    let mut running_id = trans_id;
    for (k, (unit_id, _, _)) in oriented.iter().enumerate() {
        let mut remaining: AletheClause = oriented[(k + 1)..]
            .iter()
            .map(|(_, la, lb)| AletheLit {
                atom: eq_term(la.clone(), lb.clone()),
                negated: true,
            })
            .collect();
        remaining.push(AletheLit {
            atom: eq_term(s_alethe.clone(), t_alethe.clone()),
            negated: false,
        });
        running_id = builder.step(remaining, "resolution", &[&running_id, unit_id]);
    }
    // `running_id` now names (cl (= s t)).
    let st_id = running_id;

    // Assume the disequality `(not (= s t))`. The disequality was collected as
    // `(s, t)` and BFS used that same `(s, t)`, so the derived `(= s t)` atom is
    // exactly the negated atom of this assume; the two resolve to the empty clause.
    let diseq_id = builder.assume(vec![AletheLit {
        atom: eq_term(s_alethe.clone(), t_alethe.clone()),
        negated: true,
    }]);
    builder.step(Vec::new(), "resolution", &[&st_id, &diseq_id]);

    let proof = builder.into_commands();
    if matches!(check_alethe(&proof), Ok(true)) {
        Some(proof)
    } else {
        None
    }
}

/// A classified core atom: an equality edge or the disequality.
enum CoreAtom {
    Eq(TermId, TermId),
    Diseq(TermId, TermId),
}

/// Classifies a core term as an equality `(= a b)` or a disequality
/// `(not (= s t))`. Returns `None` for any other shape.
fn classify(arena: &TermArena, term: TermId) -> Option<CoreAtom> {
    match arena.node(term) {
        TermNode::App {
            op: Op::Eq, args, ..
        } if args.len() == 2 => Some(CoreAtom::Eq(args[0], args[1])),
        TermNode::App {
            op: Op::BoolNot,
            args,
            ..
        } if args.len() == 1 => match arena.node(args[0]) {
            TermNode::App {
                op: Op::Eq,
                args: inner,
                ..
            } if inner.len() == 2 => Some(CoreAtom::Diseq(inner[0], inner[1])),
            _ => None,
        },
        _ => None,
    }
}

/// BFS an undirected equality path from `s` to `t` over `edges`, returning the
/// node sequence `[s, …, t]`, or `None` if disconnected.
fn bfs_path(s: TermId, t: TermId, edges: &[(TermId, TermId)]) -> Option<Vec<TermId>> {
    use std::collections::{BTreeMap, VecDeque};
    if s == t {
        return Some(vec![s]);
    }
    // Deterministic adjacency keyed by TermId (BTreeMap; no hashmap iteration order).
    let mut adj: BTreeMap<TermId, Vec<TermId>> = BTreeMap::new();
    for &(a, b) in edges {
        adj.entry(a).or_default().push(b);
        adj.entry(b).or_default().push(a);
    }
    let mut prev: BTreeMap<TermId, TermId> = BTreeMap::new();
    let mut visited: BTreeMap<TermId, bool> = BTreeMap::new();
    let mut queue = VecDeque::new();
    queue.push_back(s);
    visited.insert(s, true);
    while let Some(node) = queue.pop_front() {
        if node == t {
            // Reconstruct the path.
            let mut path = vec![t];
            let mut cur = t;
            while cur != s {
                let p = *prev.get(&cur)?;
                path.push(p);
                cur = p;
            }
            path.reverse();
            return Some(path);
        }
        if let Some(neighbors) = adj.get(&node) {
            for &next in neighbors {
                if !visited.get(&next).copied().unwrap_or(false) {
                    visited.insert(next, true);
                    prev.insert(next, node);
                    queue.push_back(next);
                }
            }
        }
    }
    None
}

/// Accumulates Alethe commands with deterministic fresh ids.
struct Builder {
    commands: Vec<AletheCommand>,
    next_assume: usize,
    next_step: usize,
}

impl Builder {
    fn new() -> Self {
        Self {
            commands: Vec::new(),
            next_assume: 0,
            next_step: 0,
        }
    }

    /// Emits an `assume` with a fresh `h<n>` id; returns that id.
    fn assume(&mut self, clause: AletheClause) -> String {
        let id = format!("h{}", self.next_assume);
        self.next_assume += 1;
        self.commands.push(AletheCommand::Assume {
            id: id.clone(),
            clause,
        });
        id
    }

    /// Emits a `step` with a fresh `s<n>` id; returns that id.
    fn step(&mut self, clause: AletheClause, rule: &str, premises: &[&str]) -> String {
        let id = format!("s{}", self.next_step);
        self.next_step += 1;
        self.commands.push(AletheCommand::Step {
            id: id.clone(),
            clause,
            rule: rule.to_owned(),
            premises: premises.iter().map(|p| (*p).to_owned()).collect(),
        });
        id
    }

    /// Emits the steps deriving the oriented unit clause `(cl (= pi pj))` and
    /// returns the id naming that unit. If the core stores the edge as
    /// `(= pi pj)`, the unit is the assume itself; if stored reversed
    /// `(= pj pi)`, it is an `eq_symmetric` + `resolution`.
    fn oriented_unit(
        &mut self,
        edges: &[(TermId, TermId)],
        pi: TermId,
        pj: TermId,
        lhs: &AletheTerm,
        rhs: &AletheTerm,
    ) -> Option<String> {
        let forward = edges.iter().any(|&(a, b)| a == pi && b == pj);
        let reversed = edges.iter().any(|&(a, b)| a == pj && b == pi);
        if forward {
            // assume (= pi pj) directly; its clause is the positive unit.
            Some(self.assume(vec![AletheLit {
                atom: eq_term(lhs.clone(), rhs.clone()),
                negated: false,
            }]))
        } else if reversed {
            // assume (= pj pi).
            let assume_id = self.assume(vec![AletheLit {
                atom: eq_term(rhs.clone(), lhs.clone()),
                negated: false,
            }]);
            // eq_symmetric: (cl (not (= pj pi)) (= pi pj)).
            let sym_id = self.step(
                vec![
                    AletheLit {
                        atom: eq_term(rhs.clone(), lhs.clone()),
                        negated: true,
                    },
                    AletheLit {
                        atom: eq_term(lhs.clone(), rhs.clone()),
                        negated: false,
                    },
                ],
                "eq_symmetric",
                &[],
            );
            // resolution of the symmetric clause with the assume → (cl (= pi pj)).
            Some(self.step(
                vec![AletheLit {
                    atom: eq_term(lhs.clone(), rhs.clone()),
                    negated: false,
                }],
                "resolution",
                &[&sym_id, &assume_id],
            ))
        } else {
            None // no core edge for this pair (should not happen for a BFS link)
        }
    }

    fn into_commands(self) -> Vec<AletheCommand> {
        self.commands
    }
}

/// Builds an Alethe `(= a b)` application term.
fn eq_term(a: AletheTerm, b: AletheTerm) -> AletheTerm {
    AletheTerm::App("=".to_owned(), vec![a, b])
}

/// Converts an IR term to an [`AletheTerm`], or `None` for an unsupported shape.
///
/// - a symbol becomes a [`AletheTerm::Const`] of its declared name;
/// - an `(= a b)` becomes `App("=", [conv(a), conv(b)])`;
/// - an uninterpreted application `f(args)` becomes `App(f_name, conv(args))`;
/// - a Boolean / bit-vector / integer / real constant becomes a
///   [`AletheTerm::Const`] with a stable textual form that distinguishes
///   distinct values (and, for bit-vectors, distinct widths);
/// - anything else (other operators) yields `None`.
fn term_to_alethe(arena: &TermArena, t: TermId) -> Option<AletheTerm> {
    match arena.node(t) {
        TermNode::Symbol(s) => {
            let (name, _sort) = arena.symbol(*s);
            Some(AletheTerm::Const(name.to_owned()))
        }
        TermNode::BoolConst(b) => Some(AletheTerm::Const(format!("#bool:{b}"))),
        TermNode::BvConst { width, value } => {
            Some(AletheTerm::Const(format!("#bv{width}:{value}")))
        }
        TermNode::WideBvConst(w) => Some(AletheTerm::Const(format!("#wbv:{w:?}"))),
        TermNode::IntConst(i) => Some(AletheTerm::Const(format!("#int:{i}"))),
        TermNode::RealConst(r) => Some(AletheTerm::Const(format!("#real:{r:?}"))),
        TermNode::App { op, args, .. } => match op {
            Op::Eq if args.len() == 2 => {
                let a = term_to_alethe(arena, args[0])?;
                let b = term_to_alethe(arena, args[1])?;
                Some(eq_term(a, b))
            }
            Op::Apply(func) => {
                let (name, _params, _result) = arena.function(*func);
                let name = name.to_owned();
                let mut converted = Vec::with_capacity(args.len());
                for &arg in args {
                    converted.push(term_to_alethe(arena, arg)?);
                }
                Some(AletheTerm::App(name, converted))
            }
            _ => None,
        },
    }
}

#[cfg(test)]
mod tests {
    use super::prove_qf_uf_unsat_alethe;
    use axeyum_cnf::{AletheCommand, check_alethe};
    use axeyum_ir::{Sort, TermArena};

    /// Declares a fresh `BitVec(8)` symbol variable.
    fn var(arena: &mut TermArena, name: &str) -> axeyum_ir::TermId {
        let sym = arena.declare(name, Sort::BitVec(8)).expect("declare");
        arena.var(sym)
    }

    /// `(= a b)`.
    fn eq(arena: &mut TermArena, a: axeyum_ir::TermId, b: axeyum_ir::TermId) -> axeyum_ir::TermId {
        arena.eq(a, b).expect("eq")
    }

    /// `(not (= a b))`.
    fn neq(arena: &mut TermArena, a: axeyum_ir::TermId, b: axeyum_ir::TermId) -> axeyum_ir::TermId {
        let e = eq(arena, a, b);
        arena.not(e).expect("not")
    }

    /// Asserts the last command derives the empty clause `(cl)`.
    fn last_is_empty_clause(proof: &[AletheCommand]) {
        match proof.last().expect("non-empty proof") {
            AletheCommand::Step { clause, .. } => {
                assert!(clause.is_empty(), "final step must derive the empty clause");
            }
            AletheCommand::Assume { .. } => panic!("final command must be a step"),
        }
    }

    #[test]
    fn emits_checkable_transitivity_proof() {
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let assertions = vec![
            eq(&mut arena, a, b),
            eq(&mut arena, b, c),
            neq(&mut arena, a, c),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(
            check_alethe(&proof),
            Ok(true),
            "emitted proof must independently re-check"
        );
        last_is_empty_clause(&proof);
    }

    #[test]
    fn emits_proof_for_longer_chain() {
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let d = var(&mut arena, "d");
        let assertions = vec![
            eq(&mut arena, a, b),
            eq(&mut arena, b, c),
            eq(&mut arena, c, d),
            neq(&mut arena, a, d),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(check_alethe(&proof), Ok(true));
        last_is_empty_clause(&proof);
    }

    #[test]
    fn handles_reversed_edge() {
        // First edge stored reversed: (= b a) instead of (= a b).
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let assertions = vec![
            eq(&mut arena, b, a),
            eq(&mut arena, b, c),
            neq(&mut arena, a, c),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(check_alethe(&proof), Ok(true));
        last_is_empty_clause(&proof);
    }

    #[test]
    fn handles_reversed_disequality() {
        // Disequality stored reversed: (not (= c a)) for a chain a..c.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let assertions = vec![
            eq(&mut arena, a, b),
            eq(&mut arena, b, c),
            neq(&mut arena, c, a),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(check_alethe(&proof), Ok(true));
        last_is_empty_clause(&proof);
    }

    #[test]
    fn none_for_satisfiable() {
        // a = b ∧ a ≠ c: no path from a to c, satisfiable — no proof.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let assertions = vec![eq(&mut arena, a, b), neq(&mut arena, a, c)];
        assert!(prove_qf_uf_unsat_alethe(&arena, &assertions).is_none());
    }
}
