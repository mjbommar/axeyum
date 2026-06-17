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

    let s_alethe = term_to_alethe(arena, s)?;
    let t_alethe = term_to_alethe(arena, t)?;

    let mut builder = Builder::new();

    // The disequality `(not (= s t))` assume, shared by both refutation routes.
    // The derived `(= s t)` resolves against it to the empty clause.
    let diseq_lit = AletheLit {
        atom: eq_term(s_alethe.clone(), t_alethe.clone()),
        negated: true,
    };

    // Derive `(= s t)` by transitivity and/or (nested) congruence, then resolve it
    // against the `(not (= s t))` assume to the empty clause.
    let st_id = derive_eq(&mut builder, arena, &edges, s, t)?;
    let diseq_id = builder.assume(vec![diseq_lit]);
    builder.step(Vec::new(), "resolution", &[&st_id, &diseq_id]);
    finish(builder)
}

/// Runs the assembled proof through [`axeyum_cnf::check_alethe`] and returns it
/// only if it checks (`Ok(true)`); any other outcome yields `None`. This is the
/// single self-validation gate every route funnels through.
fn finish(builder: Builder) -> Option<Vec<AletheCommand>> {
    let proof = builder.into_commands();
    if matches!(check_alethe(&proof), Ok(true)) {
        Some(proof)
    } else {
        None
    }
}

/// Emits the steps deriving the unit clause `(cl (= a b))` by transitivity over
/// the core equality graph `edges`, appending its commands to `builder` and
/// returning the id of the command whose clause is that unit (an `assume` or a
/// `resolution`/`eq_reflexive` step). Returns `None` if `a` and `b` are not
/// connected by an equality path (or a term fails to convert).
///
/// - `a == b`: emits an `eq_reflexive` step `(cl (= a a))` and returns its id.
/// - single edge already oriented `(= a b)`: returns the assume id directly.
/// - otherwise: oriented units per link, one `eq_transitive`, and a resolution
///   chain collapsing to `(cl (= a b))`, whose id is returned.
fn derive_eq(
    builder: &mut Builder,
    arena: &TermArena,
    edges: &[(TermId, TermId)],
    a: TermId,
    b: TermId,
) -> Option<String> {
    if a == b {
        // Reflexive: `(cl (= a a))`.
        let a_alethe = term_to_alethe(arena, a)?;
        return Some(builder.step(
            vec![AletheLit {
                atom: eq_term(a_alethe.clone(), a_alethe),
                negated: false,
            }],
            "eq_reflexive",
            &[],
        ));
    }
    // A transitivity path over the core equalities first; otherwise (recursively)
    // congruence — `a = f(x⃗)`, `b = f(y⃗)`, each `xᵢ = yᵢ` itself derived by this
    // same function, so nested congruence (`f(g(a)) = f(g(b))`) is handled by the
    // recursion. The transitivity attempt emits nothing when no path exists, so the
    // congruence fallback starts clean.
    if let Some(id) = derive_eq_transitivity(builder, arena, edges, a, b) {
        return Some(id);
    }
    derive_congruence(builder, arena, edges, a, b)
}

/// Emits `(cl (= a b))` via a transitivity path over the core equality graph
/// `edges`, returning its id, or `None` when `a` and `b` are not connected by such
/// a path (it emits nothing in that case, so the caller can try another route).
/// Assumes `a != b`.
fn derive_eq_transitivity(
    builder: &mut Builder,
    arena: &TermArena,
    edges: &[(TermId, TermId)],
    a: TermId,
    b: TermId,
) -> Option<String> {
    // BFS an equality path from `a` to `b` over the undirected equality graph.
    let path = bfs_path(a, b, edges)?;
    if path.len() < 2 {
        return None;
    }

    // For each consecutive pair, emit an oriented unit clause `(cl (= p_i p_{i+1}))`.
    let mut oriented: Vec<(String, AletheTerm, AletheTerm)> = Vec::new();
    for window in path.windows(2) {
        let (pi, pj) = (window[0], window[1]);
        if pi == pj {
            continue; // no edge needed
        }
        let lhs = term_to_alethe(arena, pi)?;
        let rhs = term_to_alethe(arena, pj)?;
        let id = builder.oriented_unit(edges, pi, pj, &lhs, &rhs)?;
        oriented.push((id, lhs, rhs));
    }
    if let [(only_id, _, _)] = oriented.as_slice() {
        // A single already-oriented link: the assume *is* `(cl (= a b))`.
        // (`oriented_unit` returns the assume id directly for a forward edge,
        // and a resolution-derived `(cl (= a b))` for a reversed edge.) Either
        // way `only_id` already names the unit clause we want.
        return Some(only_id.clone());
    }
    if oriented.is_empty() {
        return None;
    }

    let a_first = oriented.first().map(|(_, x, _)| x.clone())?;
    let b_last = oriented.last().map(|(_, _, y)| y.clone())?;

    // eq_transitive: (cl (not (= p0 p1)) … (not (= p_{k-1} pk)) (= a b)).
    let mut trans_clause: AletheClause = oriented
        .iter()
        .map(|(_, x, y)| AletheLit {
            atom: eq_term(x.clone(), y.clone()),
            negated: true,
        })
        .collect();
    trans_clause.push(AletheLit {
        atom: eq_term(a_first.clone(), b_last.clone()),
        negated: false,
    });
    let trans_id = builder.step(trans_clause, "eq_transitive", &[]);

    // Resolve the eq_transitive clause against each oriented unit to derive (= a b).
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
            atom: eq_term(a_first.clone(), b_last.clone()),
            negated: false,
        });
        running_id = builder.step(remaining, "resolution", &[&running_id, unit_id]);
    }
    Some(running_id)
}

/// Emits the steps deriving `(cl (= s t))` for a congruence conflict —
/// `s = f(x1..xn)` and `t = f(y1..yn)` with the same head `f` and arity — and
/// returns the id of the `(cl (= s t))` step. Each argument equality `(= xi yi)` is
/// derived by [`derive_eq`], which itself falls back to congruence, so **nested**
/// congruence (`f(g(a)) = f(g(b))`) is handled by the recursion. Returns `None` if
/// `s`/`t` are not same-head same-arity applications, an argument pair cannot be
/// derived, or a term fails to convert.
fn derive_congruence(
    builder: &mut Builder,
    arena: &TermArena,
    edges: &[(TermId, TermId)],
    s: TermId,
    t: TermId,
) -> Option<String> {
    // Both sides must be applications of the same function with the same arity.
    let (f_args, g_args): (Vec<TermId>, Vec<TermId>) = match (arena.node(s), arena.node(t)) {
        (
            TermNode::App {
                op: Op::Apply(f),
                args: fa,
                ..
            },
            TermNode::App {
                op: Op::Apply(g),
                args: ga,
                ..
            },
        ) if f == g && fa.len() == ga.len() => (fa.to_vec(), ga.to_vec()),
        _ => return None,
    };
    if f_args.is_empty() {
        return None; // nullary applications give nothing to congruence on
    }

    // For each argument pair, derive its `(cl (= xi yi))` unit and record the
    // converted argument terms for the `eq_congruent` clause.
    let mut arg_units: Vec<String> = Vec::with_capacity(f_args.len());
    let mut arg_pairs: Vec<(AletheTerm, AletheTerm)> = Vec::with_capacity(f_args.len());
    for (&xi, &yi) in f_args.iter().zip(g_args.iter()) {
        let unit_id = derive_eq(builder, arena, edges, xi, yi)?;
        let xi_alethe = term_to_alethe(arena, xi)?;
        let yi_alethe = term_to_alethe(arena, yi)?;
        arg_units.push(unit_id);
        arg_pairs.push((xi_alethe, yi_alethe));
    }

    // The two applications `f(x⃗)` and `f(y⃗)` as Alethe terms.
    let s_alethe = term_to_alethe(arena, s)?;
    let t_alethe = term_to_alethe(arena, t)?;

    // eq_congruent: (cl (not (= x1 y1)) … (not (= xn yn)) (= (f x⃗) (f y⃗))).
    let mut cong_clause: AletheClause = arg_pairs
        .iter()
        .map(|(x, y)| AletheLit {
            atom: eq_term(x.clone(), y.clone()),
            negated: true,
        })
        .collect();
    cong_clause.push(AletheLit {
        atom: eq_term(s_alethe.clone(), t_alethe.clone()),
        negated: false,
    });
    let cong_id = builder.step(cong_clause, "eq_congruent", &[]);

    // Resolve the eq_congruent clause against each per-argument unit (in order),
    // removing one negated `(= xi yi)` each time, leaving `(cl (= s t))`.
    let mut running_id = cong_id;
    for (k, unit_id) in arg_units.iter().enumerate() {
        let mut remaining: AletheClause = arg_pairs[(k + 1)..]
            .iter()
            .map(|(x, y)| AletheLit {
                atom: eq_term(x.clone(), y.clone()),
                negated: true,
            })
            .collect();
        remaining.push(AletheLit {
            atom: eq_term(s_alethe.clone(), t_alethe.clone()),
            negated: false,
        });
        running_id = builder.step(remaining, "resolution", &[&running_id, unit_id]);
    }
    Some(running_id)
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

    /// Declares a function `name : (BitVec(8) × …) -> BitVec(8)` of the given
    /// arity and returns its [`FuncId`].
    fn func(arena: &mut TermArena, name: &str, arity: usize) -> axeyum_ir::FuncId {
        let params = vec![Sort::BitVec(8); arity];
        arena
            .declare_fun(name, &params, Sort::BitVec(8))
            .expect("declare_fun")
    }

    /// `f(args)` for a previously declared function.
    fn app(
        arena: &mut TermArena,
        f: axeyum_ir::FuncId,
        args: &[axeyum_ir::TermId],
    ) -> axeyum_ir::TermId {
        arena.apply(f, args).expect("apply")
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
    fn emits_congruence_proof_unary() {
        // a = b ∧ f(a) ≠ f(b): refuted by depth-1 congruence.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let f = func(&mut arena, "f", 1);
        let fa = app(&mut arena, f, &[a]);
        let fb = app(&mut arena, f, &[b]);
        let assertions = vec![eq(&mut arena, a, b), neq(&mut arena, fa, fb)];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(
            check_alethe(&proof),
            Ok(true),
            "emitted congruence proof must independently re-check"
        );
        last_is_empty_clause(&proof);
    }

    #[test]
    fn emits_congruence_with_transitive_arg() {
        // a = b ∧ b = c ∧ f(a) ≠ f(c): the arg pair (a, c) needs transitivity.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let f = func(&mut arena, "f", 1);
        let fa = app(&mut arena, f, &[a]);
        let fc = app(&mut arena, f, &[c]);
        let assertions = vec![
            eq(&mut arena, a, b),
            eq(&mut arena, b, c),
            neq(&mut arena, fa, fc),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(check_alethe(&proof), Ok(true));
        last_is_empty_clause(&proof);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn emits_congruence_binary() {
        // a = c ∧ b = d ∧ g(a,b) ≠ g(c,d): two-argument congruence.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let d = var(&mut arena, "d");
        let g = func(&mut arena, "g", 2);
        let gab = app(&mut arena, g, &[a, b]);
        let gcd = app(&mut arena, g, &[c, d]);
        let assertions = vec![
            eq(&mut arena, a, c),
            eq(&mut arena, b, d),
            neq(&mut arena, gab, gcd),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a proof");
        assert_eq!(check_alethe(&proof), Ok(true));
        last_is_empty_clause(&proof);
    }

    #[test]
    fn emits_nested_congruence_proof() {
        // a = b ∧ f(g(a)) ≠ f(g(b)): congruence must be applied TWICE
        // (a=b ⇒ g(a)=g(b) ⇒ f(g(a))=f(g(b))), handled by the recursive derive_eq.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let f = func(&mut arena, "f", 1);
        let g = func(&mut arena, "g", 1);
        let ga = app(&mut arena, g, &[a]);
        let gb = app(&mut arena, g, &[b]);
        let fga = app(&mut arena, f, &[ga]);
        let fgb = app(&mut arena, f, &[gb]);
        let assertions = vec![eq(&mut arena, a, b), neq(&mut arena, fga, fgb)];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits a nested proof");
        assert_eq!(check_alethe(&proof), Ok(true));
        last_is_empty_clause(&proof);
    }

    #[test]
    fn none_for_unrelated_function_diseq() {
        // f(a) ≠ f(b) with NO a = b: the args are unconnected — no proof.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let f = func(&mut arena, "f", 1);
        let fa = app(&mut arena, f, &[a]);
        let fb = app(&mut arena, f, &[b]);
        let assertions = vec![neq(&mut arena, fa, fb)];
        assert!(prove_qf_uf_unsat_alethe(&arena, &assertions).is_none());
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
