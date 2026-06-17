//! Alethe proof **emission** for congruence-based EUF refutations (Track 3, the
//! producer counterpart to [`axeyum_cnf::check_alethe`]).
//!
//! The solver already *checks* Alethe proofs; this module *emits* one for a class
//! of EUF conflicts — an equality derivation (transitivity and/or congruence)
//! refuting a disequality. Emission is **self-validating**: every proof this
//! builds is run through [`axeyum_cnf::check_alethe`] before being returned, so a
//! buggy build is *rejected* (returns `None`), never returned wrong. The
//! acceptance test is therefore the correctness gate: a returned proof has been
//! independently re-checked and derives the empty clause `(cl)`.
//!
//! The conflict core comes from [`crate::prove_unsat_by_congruence`] — a subset of
//! the original assertions that is UNSAT by congruence. For the slice handled here
//! that core is a set of equality terms `(= a b)` plus exactly one disequality term
//! `(not (= s t))`.
//!
//! Emission is driven by the e-graph's **structured explanation**
//! ([`axeyum_egraph::EGraph::explain_steps`]). We rebuild a small e-graph over the
//! core (a term↔node bridge), merge the asserted equalities, then walk the proof
//! steps connecting the disequality's two sides: each [`ProofStep::Input`] is a
//! directly-asserted equality (oriented with `eq_symmetric` when the path runs the
//! other way), and each [`ProofStep::Congruence`] is an `eq_congruent` over its
//! recursively-derived argument equalities. The per-step units are threaded through
//! one `eq_transitive` into `(= s t)`, which resolves against the disequality assume
//! to the empty clause. Because the e-graph closes *mixed* transitivity and
//! congruence (e.g. `f(a) = c ∧ a = b ⇒ f(b) = c`), this handles conflicts the
//! earlier edge-BFS emitter could not.

use std::collections::HashMap;

use axeyum_cnf::{AletheClause, AletheCommand, AletheLit, AletheTerm, check_alethe};
use axeyum_egraph::{EGraph, ENodeId, ProofStep};
use axeyum_ir::{Op, TermArena, TermId, TermNode};

/// Emits a checkable Alethe refutation for a congruence-based EUF conflict in
/// `assertions`, or `None` if the query is not refuted by congruence or the
/// conflict is not a single-disequality slice this emitter handles.
///
/// The returned proof, when non-`None`, is guaranteed to pass
/// [`axeyum_cnf::check_alethe`] (it is self-validated before return) and to derive
/// the empty clause `(cl)`. `None` is returned when:
///
/// - [`crate::prove_unsat_by_congruence`] does not refute the assertions;
/// - the conflict core is not exactly some equality terms `(= a b)` plus one
///   disequality `(not (= s t))`;
/// - the e-graph does not actually make the disequality's two sides equal
///   (defensive — should not happen for a real congruence conflict);
/// - a core term references an operator or constant the term→Alethe converter does
///   not cover; or
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

    // Classify the core into equality edges (with their assertion index, the
    // e-graph `merge` reason) and exactly one disequality.
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

    // Build an e-graph over the core terms. **All** terms (every equality side, the
    // disequality sides, and their subterms) are added *before* any merge, so that
    // congruent applications like `f(a)` and `f(b)` exist as distinct nodes and the
    // proof forest records the congruence edge between them — otherwise hash-consing
    // after a merge would collapse them and hide the congruence step.
    let mut bridge = Bridge2::new();
    let mut edge_nodes: Vec<(ENodeId, ENodeId)> = Vec::with_capacity(edges.len());
    for &(a, b) in &edges {
        let na = bridge.add_term(arena, a)?;
        let nb = bridge.add_term(arena, b)?;
        edge_nodes.push((na, nb));
    }
    let ns = bridge.add_term(arena, s)?;
    let nt = bridge.add_term(arena, t)?;

    // Now merge the asserted equalities. The merge reason is the edge index, which a
    // `ProofStep::Input` carries back; we recover the IR pair from `merges[reason]`.
    for (&(na, nb), &(a, b)) in edge_nodes.iter().zip(edges.iter()) {
        let reason = u32::try_from(bridge.merges.len()).ok()?;
        bridge.egraph.merge(na, nb, reason);
        bridge.merges.push((a, b));
    }
    if !bridge.egraph.equal(ns, nt) {
        return None; // not actually a congruence conflict (defensive)
    }

    let s_alethe = term_to_alethe(arena, s)?;
    let t_alethe = term_to_alethe(arena, t)?;

    let mut builder = Builder::new();

    // Derive `(= s t)` from the structured explanation, then resolve it against the
    // `(not (= s t))` assume to the empty clause.
    let mut ctx = StepCtx {
        arena,
        bridge: &bridge,
    };
    let st_id = derive_eq_via_steps(&mut builder, &mut ctx, ns, nt)?;
    let diseq_id = builder.assume(vec![AletheLit {
        atom: eq_term(s_alethe, t_alethe),
        negated: true,
    }]);
    builder.step(Vec::new(), "resolution", &[&st_id, &diseq_id]);
    finish(builder)
}

/// Runs the assembled proof through [`axeyum_cnf::check_alethe`] and returns it only
/// if it checks (`Ok(true)`); any other outcome yields `None`. This is the single
/// self-validation gate every route funnels through.
fn finish(builder: Builder) -> Option<Vec<AletheCommand>> {
    let proof = builder.into_commands();
    if matches!(check_alethe(&proof), Ok(true)) {
        Some(proof)
    } else {
        None
    }
}

/// Read-only context threaded through the recursive emitter: the IR arena and the
/// term↔e-graph bridge whose [`EGraph::explain_steps`] drives derivation.
struct StepCtx<'a> {
    arena: &'a TermArena,
    bridge: &'a Bridge2,
}

/// Emits the steps deriving the unit clause `(cl (= term(na) term(nb)))` by walking
/// [`EGraph::explain_steps`]`(na, nb)`, appending its commands to `builder` and
/// returning the id of the command naming that unit. Returns `None` if any e-node
/// fails to convert back to a term/Alethe term.
///
/// - `na == nb`: emits `eq_reflexive` `(cl (= t t))` and returns its id.
/// - otherwise: for each proof step, an oriented unit `(cl (= x y))` walking
///   `na → nb` — a [`ProofStep::Input`] is the asserted equality (flipped with
///   `eq_symmetric` + `resolution` when the path runs the other way); a
///   [`ProofStep::Congruence`] is an `eq_congruent` over its recursively-derived
///   argument units. A single step is returned directly; multiple steps are
///   threaded through one `eq_transitive` and a resolution into `(cl (= na nb))`.
fn derive_eq_via_steps(
    builder: &mut Builder,
    ctx: &mut StepCtx,
    na: ENodeId,
    nb: ENodeId,
) -> Option<String> {
    if na == nb {
        let a_alethe = ctx.node_alethe(na)?;
        return Some(builder.step(
            vec![AletheLit {
                atom: eq_term(a_alethe.clone(), a_alethe),
                negated: false,
            }],
            "eq_reflexive",
            &[],
        ));
    }

    let steps = ctx.bridge.egraph.explain_steps(na, nb);
    if steps.is_empty() {
        // Distinct nodes the e-graph reports as equal but with no proof path: emit
        // nothing and bail (the self-check would reject any fabricated unit anyway).
        return None;
    }

    // `explain_steps` returns the `a`-side path (na → LCA) followed by the `b`-side
    // path (nb → LCA), so the two halves meet at the LCA and the `b` half is stated
    // in the opposite direction to the na → nb walk. Order the steps into a single
    // na → nb chain by greedily following the step incident to the current node, and
    // orient each step's unit accordingly so the `eq_transitive` middles line up.
    let mut remaining: Vec<&ProofStep> = steps.iter().collect();
    let mut cur = na;
    let mut links: Vec<Link> = Vec::with_capacity(steps.len());
    while !remaining.is_empty() {
        // The remaining step incident to `cur` (every step relates two nodes; the
        // chain is simple, so exactly one remaining step touches `cur`).
        let pos = remaining.iter().position(|s| {
            let (sa, sb) = step_endpoints(s);
            sa == cur || sb == cur
        })?;
        let step = remaining.remove(pos);
        let (sa, sb) = step_endpoints(step);
        let (from, to) = if sa == cur { (sa, sb) } else { (sb, sa) };
        let from_alethe = ctx.node_alethe(from)?;
        let to_alethe = ctx.node_alethe(to)?;
        let unit_id = emit_step_unit(builder, ctx, step, from, to, &from_alethe, &to_alethe)?;
        links.push(Link {
            id: unit_id,
            lhs: from_alethe,
            rhs: to_alethe,
        });
        cur = to;
    }

    if let [only] = links.as_slice() {
        return Some(only.id.clone()); // a single oriented unit is already `(= na nb)`
    }
    chain_transitive(builder, &links)
}

/// Emits the oriented unit `(cl (= term(from) term(to)))` for one proof step,
/// returning its command id.
fn emit_step_unit(
    builder: &mut Builder,
    ctx: &mut StepCtx,
    step: &ProofStep,
    from: ENodeId,
    to: ENodeId,
    from_alethe: &AletheTerm,
    to_alethe: &AletheTerm,
) -> Option<String> {
    match step {
        ProofStep::Input { a, b, reason } => {
            // The asserted equality is `edges[reason]`, an IR term pair `(= ea eb)`.
            // Its e-nodes are `a`/`b`; the path may run either way through them.
            let (ea, eb) = *ctx.bridge.merges.get(*reason as usize)?;
            let lhs_alethe = term_to_alethe(ctx.arena, ea)?;
            let rhs_alethe = term_to_alethe(ctx.arena, eb)?;
            // Assume the stored equality `(= ea eb)`.
            let assume_id = builder.assume(vec![AletheLit {
                atom: eq_term(lhs_alethe.clone(), rhs_alethe.clone()),
                negated: false,
            }]);
            // The assume orients `node(ea) → node(eb)`. If that already matches the
            // path direction `from → to`, return it; otherwise flip via eq_symmetric.
            let stored_forward = ctx.bridge.term_to_node.get(&ea).copied() == Some(from);
            debug_assert!(
                (*a == from && *b == to) || (*a == to && *b == from),
                "input step endpoints are the oriented pair"
            );
            if stored_forward {
                Some(assume_id)
            } else {
                Some(builder.flip_unit(
                    &assume_id,
                    &lhs_alethe,
                    &rhs_alethe,
                    from_alethe,
                    to_alethe,
                ))
            }
        }
        ProofStep::Congruence { args, .. } => {
            // Derive each argument equality, oriented `from`-side arg → `to`-side arg.
            // `from`/`to` are the two applications; pair their arguments by position.
            let from_args = ctx.bridge.egraph.args(from).to_vec();
            let to_args = ctx.bridge.egraph.args(to).to_vec();
            if from_args.len() != to_args.len() || from_args.len() != args.len() {
                return None; // arity mismatch (defensive)
            }
            let mut arg_units: Vec<String> = Vec::with_capacity(from_args.len());
            let mut arg_pairs: Vec<(AletheTerm, AletheTerm)> = Vec::with_capacity(from_args.len());
            for (&xa, &xb) in from_args.iter().zip(to_args.iter()) {
                let unit_id = derive_eq_via_steps(builder, ctx, xa, xb)?;
                let lhs_alethe = ctx.node_alethe(xa)?;
                let rhs_alethe = ctx.node_alethe(xb)?;
                arg_units.push(unit_id);
                arg_pairs.push((lhs_alethe, rhs_alethe));
            }
            Some(builder.congruence(&arg_units, &arg_pairs, from_alethe, to_alethe))
        }
    }
}

/// Threads the oriented links left-to-right through one `eq_transitive` plus a
/// resolution, deriving `(cl (= lhs(first) rhs(last)))`. Assumes `links.len() >= 2`.
fn chain_transitive(builder: &mut Builder, links: &[Link]) -> Option<String> {
    let a_first = links.first()?.lhs.clone();
    let b_last = links.last()?.rhs.clone();

    // eq_transitive: (cl (not (= p0 p1)) … (not (= p_{k-1} pk)) (= a b)).
    let mut trans_clause: AletheClause = links
        .iter()
        .map(|l| AletheLit {
            atom: eq_term(l.lhs.clone(), l.rhs.clone()),
            negated: true,
        })
        .collect();
    trans_clause.push(AletheLit {
        atom: eq_term(a_first.clone(), b_last.clone()),
        negated: false,
    });
    let trans_id = builder.step(trans_clause, "eq_transitive", &[]);

    // Resolve the eq_transitive clause against every oriented unit in one step.
    let mut premises: Vec<&str> = Vec::with_capacity(links.len() + 1);
    premises.push(&trans_id);
    for l in links {
        premises.push(&l.id);
    }
    Some(builder.step(
        vec![AletheLit {
            atom: eq_term(a_first, b_last),
            negated: false,
        }],
        "resolution",
        &premises,
    ))
}

/// One oriented equality link `(= lhs rhs)` along a derivation chain, with the id of
/// the command whose unit clause is that equality.
struct Link {
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

/// What a `decl` identifies in the term→e-graph bridge: a symbol, an uninterpreted
/// function, an interpreted operator (treated uninterpreted), or a literal constant.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum DeclKey {
    Symbol(usize),
    Func(usize),
    Op(String),
    Const(String),
}

/// Builds an e-graph over the core terms, mirroring [`crate::euf_egraph`]'s bridge:
/// every symbol/function/operator/constant gets a distinct `decl`, so the e-graph's
/// congruence matches the terms' structure. Keeps a term↔node map so the structured
/// explanation can be converted back to Alethe terms.
struct Bridge2 {
    egraph: EGraph,
    /// First term seen per e-node, for converting a node back to an IR term.
    node_to_term: HashMap<ENodeId, TermId>,
    term_to_node: HashMap<TermId, ENodeId>,
    decls: HashMap<DeclKey, u32>,
    /// Per merge reason index: the asserted equality's IR term pair.
    merges: Vec<(TermId, TermId)>,
    next_decl: u32,
}

impl Bridge2 {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            node_to_term: HashMap::new(),
            term_to_node: HashMap::new(),
            decls: HashMap::new(),
            merges: Vec::new(),
            next_decl: 0,
        }
    }

    /// A stable `decl` id for `key`.
    fn decl(&mut self, key: DeclKey) -> u32 {
        if let Some(&d) = self.decls.get(&key) {
            return d;
        }
        let d = self.next_decl;
        self.next_decl += 1;
        self.decls.insert(key, d);
        d
    }

    /// The e-node for `term`, creating it (and its subterms) on first use. Returns
    /// `None` only for a term shape it cannot convert (kept symmetric with
    /// [`term_to_alethe`], so a node that fails here would also fail conversion).
    fn add_term(&mut self, arena: &TermArena, term: TermId) -> Option<ENodeId> {
        if let Some(&n) = self.term_to_node.get(&term) {
            return Some(n);
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.decl(DeclKey::Symbol(s.index()));
                self.egraph.add(decl, &[])
            }
            TermNode::BoolConst(_)
            | TermNode::BvConst { .. }
            | TermNode::WideBvConst(_)
            | TermNode::IntConst(_)
            | TermNode::RealConst(_) => {
                let key = DeclKey::Const(format!("{:?}", arena.node(term)));
                let decl = self.decl(key);
                self.egraph.add(decl, &[])
            }
            TermNode::App { op, args } => {
                let op = *op;
                let args = args.clone();
                let mut child_nodes = Vec::with_capacity(args.len());
                for &a in &args {
                    child_nodes.push(self.add_term(arena, a)?);
                }
                let key = match op {
                    Op::Apply(func) => DeclKey::Func(func.index()),
                    other => DeclKey::Op(format!("{other:?}")),
                };
                let decl = self.decl(key);
                self.egraph.add(decl, &child_nodes)
            }
        };
        self.term_to_node.insert(term, node);
        self.node_to_term.entry(node).or_insert(term);
        Some(node)
    }
}

impl StepCtx<'_> {
    /// The Alethe term for e-node `n`, via the first term recorded for it.
    fn node_alethe(&self, n: ENodeId) -> Option<AletheTerm> {
        let term = *self.bridge.node_to_term.get(&n)?;
        term_to_alethe(self.arena, term)
    }
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

    /// Flips a unit `(cl (= ea eb))` (named `unit_id`) into `(cl (= from to))` where
    /// `(from, to)` is `(eb, ea)` — via `eq_symmetric` + `resolution`. Returns the id
    /// of the flipped unit. `ea`/`eb` are the stored equality's sides as Alethe terms.
    fn flip_unit(
        &mut self,
        unit_id: &str,
        ea: &AletheTerm,
        eb: &AletheTerm,
        from: &AletheTerm,
        to: &AletheTerm,
    ) -> String {
        // eq_symmetric: (cl (not (= ea eb)) (= eb ea)).
        let sym_id = self.step(
            vec![
                AletheLit {
                    atom: eq_term(ea.clone(), eb.clone()),
                    negated: true,
                },
                AletheLit {
                    atom: eq_term(eb.clone(), ea.clone()),
                    negated: false,
                },
            ],
            "eq_symmetric",
            &[],
        );
        // resolution of the symmetric clause with the assume → (cl (= eb ea)).
        self.step(
            vec![AletheLit {
                atom: eq_term(from.clone(), to.clone()),
                negated: false,
            }],
            "resolution",
            &[&sym_id, unit_id],
        )
    }

    /// Emits `eq_congruent` over the argument units plus a resolution, deriving
    /// `(cl (= from to))` where `from`/`to` are the two applications and `arg_pairs`
    /// their argument equalities (each derived by `arg_units`, in order). Returns the
    /// id of the `(cl (= from to))` step.
    fn congruence(
        &mut self,
        arg_units: &[String],
        arg_pairs: &[(AletheTerm, AletheTerm)],
        from: &AletheTerm,
        to: &AletheTerm,
    ) -> String {
        // eq_congruent: (cl (not (= a1 b1)) … (not (= an bn)) (= from to)).
        let mut cong_clause: AletheClause = arg_pairs
            .iter()
            .map(|(x, y)| AletheLit {
                atom: eq_term(x.clone(), y.clone()),
                negated: true,
            })
            .collect();
        cong_clause.push(AletheLit {
            atom: eq_term(from.clone(), to.clone()),
            negated: false,
        });
        let cong_id = self.step(cong_clause, "eq_congruent", &[]);

        // Resolve the congruence clause against every argument unit in one step.
        let mut premises: Vec<&str> = Vec::with_capacity(arg_units.len() + 1);
        premises.push(&cong_id);
        for u in arg_units {
            premises.push(u);
        }
        self.step(
            vec![AletheLit {
                atom: eq_term(from.clone(), to.clone()),
                negated: false,
            }],
            "resolution",
            &premises,
        )
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
///   [`AletheTerm::Const`] with a stable textual form that distinguishes distinct
///   values (and, for bit-vectors, distinct widths);
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
            // Any other interpreted operator is treated as an uninterpreted function
            // symbol — matching the e-graph's congruence abstraction — so congruence
            // over it, e.g. array `select` extensionality (`a = b ⇒ select(a,i) =
            // select(b,i)`), emits a checkable proof. The `{op:?}` head is stable per
            // operator kind, so two applications of the same op share a head.
            _ => {
                let name = format!("{op:?}");
                let mut converted = Vec::with_capacity(args.len());
                for &arg in args {
                    converted.push(term_to_alethe(arena, arg)?);
                }
                Some(AletheTerm::App(name, converted))
            }
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

    /// Declares a function `name : (BitVec(8) × …) -> BitVec(8)` of the given arity
    /// and returns its [`FuncId`].
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
    fn emits_proof_for_array_extensionality() {
        // a = b ∧ select(a, i) ≠ select(b, i): congruence over `select` (treated as
        // an uninterpreted function) refutes it, and the emitter produces a
        // check_alethe-accepted proof — interpreted ops now convert to Alethe terms.
        let mut arena = TermArena::new();
        let a = arena.array_var("a", 8, 8).unwrap();
        let b = arena.array_var("b", 8, 8).unwrap();
        let i = arena.bv_var("i", 8).unwrap();
        let sa = arena.select(a, i).unwrap();
        let sb = arena.select(b, i).unwrap();
        let e1 = arena.eq(a, b).unwrap();
        let ne = {
            let e = arena.eq(sa, sb).unwrap();
            arena.not(e).unwrap()
        };
        let proof = prove_qf_uf_unsat_alethe(&arena, &[e1, ne])
            .expect("emits an array extensionality proof");
        assert_eq!(check_alethe(&proof), Ok(true));
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
        // (a=b ⇒ g(a)=g(b) ⇒ f(g(a))=f(g(b))), handled by the recursive derivation.
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
    fn emits_mixed_congruence_transitivity_proof() {
        // f(a) = c ∧ a = b ∧ f(b) ≠ c: the disequality's sides f(b) and c become
        // equal only through MIXED congruence-in-transitivity — f(b) = f(a) (by
        // congruence from a = b) = c (asserted). The old edge-BFS emitter returned
        // None on this; explain_steps drives it.
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let c = var(&mut arena, "c");
        let f = func(&mut arena, "f", 1);
        let fa = app(&mut arena, f, &[a]);
        let fb = app(&mut arena, f, &[b]);
        let assertions = vec![
            eq(&mut arena, fa, c),
            eq(&mut arena, a, b),
            neq(&mut arena, fb, c),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits the mixed proof");
        assert_eq!(
            check_alethe(&proof),
            Ok(true),
            "mixed congruence/transitivity proof must independently re-check"
        );
        last_is_empty_clause(&proof);
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn emits_congruence_chain() {
        // a = b ∧ g(a) = d ∧ d = e ∧ g(b) ≠ e: congruence (g(b) = g(a) = d) then
        // transitivity (d = e).
        let mut arena = TermArena::new();
        let a = var(&mut arena, "a");
        let b = var(&mut arena, "b");
        let d = var(&mut arena, "d");
        let e = var(&mut arena, "e");
        let g = func(&mut arena, "g", 1);
        let ga = app(&mut arena, g, &[a]);
        let gb = app(&mut arena, g, &[b]);
        let assertions = vec![
            eq(&mut arena, a, b),
            eq(&mut arena, ga, d),
            eq(&mut arena, d, e),
            neq(&mut arena, gb, e),
        ];
        let proof = prove_qf_uf_unsat_alethe(&arena, &assertions).expect("emits the chain proof");
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
