//! E-matching quantifier instantiation on the e-graph keystone (Track 2, P2.6).
//!
//! [`instantiate_forall_via_egraph`] is the keystone-driven path for instantiating
//! a universal `∀x. body`: it builds an [`EGraph`] over the ground terms, selects a
//! trigger — a function-application subterm mentioning the bound variable, which
//! may be **nested** (`f(g(x))`) or **multi-argument with ground parts**
//! (`g(x, a)`) — e-matches it against the e-graph **modulo congruence**
//! ([`EGraph::ematch`]), and for each match substitutes the bound variable with a
//! representative of the matched argument class, producing the ground instances to
//! add and re-check.
//!
//! Matching on the e-graph is congruence-aware for free: if the ground terms force
//! `a = b`, then `f(a)` and `f(b)` are one class and the trigger fires once, so the
//! instances follow the *semantic* term structure, not the syntactic one. This is
//! the migration of trigger instantiation onto the backtrackable, independently
//! checkable keystone (vs the bespoke congruence closure the existing
//! `axeyum_rewrite::instantiate_with_triggers` carries); deeper triggers,
//! inference, and the full instantiation loop build on it.

use std::collections::{HashMap, HashSet};

use axeyum_egraph::{EGraph, ENodeId, Pattern};
use axeyum_ir::{FuncId, Op, SymbolId, TermArena, TermId, TermNode};
use axeyum_rewrite::replace_subterms;

// Native uses the std clock; wasm uses the `web_time` drop-in (ADR-0017).
#[cfg(not(target_arch = "wasm32"))]
use std::time::Instant;
#[cfg(target_arch = "wasm32")]
use web_time::Instant;

use crate::auto::check_auto;
use crate::backend::{CheckResult, SolverConfig, SolverError, UnknownKind, UnknownReason};

/// Default e-matching instantiation rounds before giving up (`unknown`).
const MAX_INSTANTIATION_ROUNDS: usize = 8;

/// Deterministic cap on accumulated ground terms: e-matching a universal whose
/// instances generate ever-deeper terms (e.g. `∀x.(x≤y ∨ x≥y+1)` ⇒ `y, y+1, y+2, …`)
/// can explode a single round's `check_auto`, so the loop bails to `unknown` past this
/// many ground terms even with no wall-clock budget (the "never hang" rule).
const MAX_GROUND_TERMS: usize = 8192;

/// Tries to refute a (possibly quantified) conjunction by **e-matching
/// instantiation on the e-graph** (Track 2, P2.6): it separates the ground
/// assertions from the universals, and repeatedly instantiates each universal over
/// the current ground terms ([`instantiate_forall_via_egraph`]), adds the fresh
/// instances, and re-checks the ground set with [`check_auto`] — until the ground
/// set is `unsat` (⇒ the original is `unsat`, since the universals entail every
/// instance), a round adds no new instance (instantiation fixpoint), or the round
/// budget is exhausted.
///
/// **Sound, incomplete:** a ground `unsat` is a real refutation; otherwise the
/// result is `unknown` (e-matching may simply not have found the refuting
/// instance). Quantifier-free inputs go straight to [`check_auto`].
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground solver.
pub fn prove_quantified_unsat_via_egraph(
    arena: &mut TermArena,
    assertions: &[TermId],
    config: &SolverConfig,
) -> Result<CheckResult, SolverError> {
    let mut ground: Vec<TermId> = Vec::new();
    let mut foralls: Vec<TermId> = Vec::new();
    for &a in assertions {
        if matches!(arena.node(a), TermNode::App { op, .. } if matches!(op, Op::Forall(_))) {
            foralls.push(a);
        } else {
            ground.push(a);
        }
    }
    if foralls.is_empty() {
        return check_auto(arena, &ground, config);
    }

    // Closed-universal falsification (P2.6 slice-6, census-justified lever).
    //
    // The e-matching round loop below only refutes a `∀x⃗. body` by *weakening*:
    // it adds ground instances `body[x⃗ := witness]` drawn from function-application
    // triggers matched against the ground terms. A **closed** universal — one whose
    // body is quantifier-free and mentions no symbol beyond its own bound variables
    // — has no free parameters to match against and, for the shapes in the measured
    // corpus (e.g. `∀A B C D. (A=B∧C=D) ∨ (A=C∧B=D)`), no function-application
    // trigger at all, so `select_triggers` yields nothing and the loop returns
    // `unknown` no matter how large the round/instance budget is. This is not
    // depth-starvation; it is a distinct instantiation-strategy gap the census of
    // the bv-cvc5-quantified division surfaced.
    //
    // A closed universal is a *sentence*: `∀x⃗. body` is a constant truth value.
    // It is **false** iff `∃x⃗. ¬body` holds, i.e. iff `¬body[x⃗ := c⃗]` is
    // satisfiable for fresh constants `c⃗` (the ground solver picks the falsifying
    // witness). A false top-level assertion makes the whole conjunction `unsat`,
    // regardless of the other assertions — so a satisfiable `¬body[c⃗]` transfers
    // soundly to `Unsat` for the original query. This is **exact** for the closed
    // universal (a closed sentence has no other truth value) and **terminates** in
    // a single bounded quantifier-free `check_auto` call (no fixpoint, no growth).
    // The valid direction (`¬body[c⃗]` unsat ⇒ the universal is `true`) is already
    // handled upstream by `quant_valid_universal::eliminate_valid_universals`, so
    // only the refuting direction is taken here; anything but a definite `Sat`
    // (including a `check_auto` `unknown` on a hard body) declines and falls
    // through to the e-matching loop, never a wrong verdict.
    for &quantifier in &foralls {
        if let Some(CheckResult::Unsat) = refute_closed_universal(arena, quantifier, config)? {
            return Ok(CheckResult::Unsat);
        }
    }

    // Honor the wall-clock budget + a deterministic ground-size cap so an exploding
    // instantiation degrades to a graceful `unknown`, never spins (the "never hang" rule).
    let deadline = config.timeout.and_then(|t| Instant::now().checked_add(t));
    let budget_exhausted = |ground: &[TermId]| {
        deadline.is_some_and(|d| Instant::now() >= d) || ground.len() > MAX_GROUND_TERMS
    };
    let mut seen: HashSet<TermId> = ground.iter().copied().collect();
    for _ in 0..MAX_INSTANTIATION_ROUNDS {
        if budget_exhausted(&ground) {
            return Ok(CheckResult::Unknown(UnknownReason {
                kind: UnknownKind::ResourceLimit,
                detail: "e-matching: instantiation budget (time or ground-term count) exhausted"
                    .to_owned(),
            }));
        }
        // A ground refutation at any point is a refutation of the whole problem.
        if matches!(check_auto(arena, &ground, config)?, CheckResult::Unsat) {
            return Ok(CheckResult::Unsat);
        }
        // Instantiate every universal over the current ground terms.
        let mut added = false;
        let universals = foralls.clone();
        for quantifier in universals {
            for instance in instantiate_forall_via_egraph(arena, &ground, quantifier) {
                if seen.insert(instance) {
                    ground.push(instance);
                    added = true;
                }
            }
        }
        if !added {
            break; // instantiation fixpoint: no new ground facts
        }
    }
    // Final ground check (may now be unsat with the last round's instances).
    match check_auto(arena, &ground, config)? {
        CheckResult::Unsat => Ok(CheckResult::Unsat),
        _ => Ok(CheckResult::Unknown(UnknownReason {
            kind: UnknownKind::Incomplete,
            detail: "e-matching instantiation did not refute within the round budget".to_owned(),
        })),
    }
}

/// Instantiates the universal `forall_term` by e-matching a trigger against the
/// `ground` terms, returning the ground instances of its body. Returns an empty
/// vector when `forall_term` is not a universal, has no trigger covering all bound
/// variables, or the trigger's symbols do not occur in the ground terms.
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn instantiate_forall_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Vec<TermId> {
    let Some((vars, body, tuples)) = witness_tuples_via_egraph(arena, ground, forall_term) else {
        return Vec::new();
    };
    let var_terms: Vec<TermId> = vars.iter().map(|&v| arena.var(v)).collect();
    let mut instances = Vec::new();
    for tuple in &tuples {
        let replacements: HashMap<TermId, TermId> = var_terms
            .iter()
            .copied()
            .zip(tuple.iter().copied())
            .collect();
        let mut memo = HashMap::new();
        if let Ok(instance) = replace_subterms(arena, body, &replacements, &mut memo) {
            instances.push(instance);
        }
    }
    instances.sort_by_key(|t| t.index());
    instances.dedup();
    instances
}

/// E-matches the universal `forall_term`'s trigger(s) against the `ground` terms
/// and returns, in addition to the bound variables and quantifier-free body, the
/// **witness tuples** — one ground term per bound variable, in binder order
/// (outermost first) — that the e-matching selects. Tuples are deterministically
/// ordered and de-duplicated.
///
/// This is the witness-tuple source the Alethe quantifier emitter
/// ([`crate::prove_quant_unsat_alethe`]) consumes when the brute-force cartesian
/// search would blow its candidate cap: e-matching is trigger-driven, so it scales
/// to many ground terms / multiple binders where the cartesian product does not.
/// The returned tuples are *candidates* — the caller validates that some subset
/// actually refutes the ground set before emitting a proof, so an unhelpful match
/// set is rejected cleanly, never turned into a bad proof.
///
/// Returns `None` when `forall_term` is not a universal, has no trigger covering
/// all bound variables, or no complete witness tuple is found (the trigger's
/// symbols do not occur in the ground terms).
///
/// # Panics
///
/// Panics only if the quantifier binds more than `u32::MAX` variables (which no
/// real input does).
#[must_use]
pub fn witness_tuples_via_egraph(
    arena: &mut TermArena,
    ground: &[TermId],
    forall_term: TermId,
) -> Option<(Vec<SymbolId>, TermId, Vec<Vec<TermId>>)> {
    // Peel the (possibly nested) universal prefix `∀x. ∀y. … body`.
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return None;
    }
    let var_index: HashMap<SymbolId, u32> = vars
        .iter()
        .enumerate()
        .map(|(i, &v)| (v, u32::try_from(i).expect("variable count fits u32")))
        .collect();

    // Infer a (possibly multi-pattern) trigger: a set of function-application
    // subterms whose bound variables together cover all of them. A single term is
    // used when one covers all variables; otherwise a greedy set cover (matched
    // and joined below) handles patterns like `∀x,y. f(x) = g(y)`.
    let triggers = select_triggers(arena, body, &var_index);
    if triggers.is_empty() {
        return None;
    }

    let mut bridge = InstBridge::new();
    for &g in ground {
        bridge.add_term(arena, g);
        // A top-level ground equality `(= s t)` asserts s = t — merge it so matching
        // is genuinely modulo the ground congruence.
        if let TermNode::App { op, args } = arena.node(g)
            && matches!(op, Op::Eq)
            && args.len() == 2
        {
            let (s, t) = (args[0], args[1]);
            let ns = bridge.add_term(arena, s);
            let nt = bridge.add_term(arena, t);
            bridge.egraph.merge(ns, nt, 0);
        }
    }

    // Match each trigger and join the per-trigger substitutions into full
    // substitutions consistent on shared variables.
    let nvars = vars.len();
    let mut joined: Vec<Vec<Option<ENodeId>>> = vec![vec![None; nvars]];
    for trigger in triggers {
        let pattern = bridge.trigger_to_pattern(arena, trigger, &var_index);
        let matches = bridge.egraph.ematch(&pattern);
        let mut next = Vec::new();
        for partial in &joined {
            for m in &matches {
                if let Some(merged) = merge_substitutions(partial, m) {
                    next.push(merged);
                }
            }
        }
        joined = next;
        if joined.is_empty() {
            return None;
        }
    }

    let mut tuples: Vec<Vec<TermId>> = Vec::new();
    for subst in joined {
        // Build the witness tuple from every bound variable's matched class
        // representative; skip incomplete matches.
        let mut tuple: Vec<TermId> = Vec::with_capacity(nvars);
        let complete = (0..nvars).all(|i| {
            if let Some(repr) = subst
                .get(i)
                .copied()
                .flatten()
                .and_then(|class| bridge.repr_term.get(&class).copied())
            {
                tuple.push(repr);
                true
            } else {
                false
            }
        });
        if complete {
            tuples.push(tuple);
        }
    }
    // Deterministic order and de-dup (tuples compare lexicographically by index).
    tuples.sort_by(|x, y| x.iter().map(|t| t.index()).cmp(y.iter().map(|t| t.index())));
    tuples.dedup();
    Some((vars, body, tuples))
}

/// Peels the universal prefix `∀v1. ∀v2. … body`, returning the bound variables
/// (outer first) and the innermost non-quantified body.
fn peel_foralls(arena: &TermArena, mut term: TermId) -> (Vec<SymbolId>, TermId) {
    let mut vars = Vec::new();
    while let Some((var, body)) = as_forall(arena, term) {
        vars.push(var);
        term = body;
    }
    (vars, term)
}

/// Decomposes a `(forall x body)` term into its bound variable and body.
fn as_forall(arena: &TermArena, term: TermId) -> Option<(SymbolId, TermId)> {
    match arena.node(term) {
        TermNode::App { op, args } if matches!(op, Op::Forall(_)) && args.len() == 1 => {
            let Op::Forall(var) = op else {
                unreachable!("matched Forall above")
            };
            Some((*var, args[0]))
        }
        _ => None,
    }
}

/// Refutes a **closed** top-level universal `∀x⃗. body` by falsifying its body.
///
/// Returns `Ok(Some(Unsat))` when `forall_term` is a closed universal (a
/// quantifier-free body mentioning no symbol outside its own bound variables) and
/// `¬body[x⃗ := c⃗]` is satisfiable for fresh constants `c⃗` — a witness that the
/// closed sentence `∀x⃗. body` is *false*, hence the whole query is `unsat`.
/// Returns `Ok(None)` when the shape does not apply (not a universal, an open or
/// still-quantified body) or the falsification sub-check is not a definite `Sat`
/// (`unsat` ⇒ the universal is valid, already handled upstream; `unknown` ⇒ decline
/// so the e-matching loop still runs). Never returns a non-`Unsat` `CheckResult`.
///
/// # Errors
///
/// Propagates any [`SolverError`] from the ground [`check_auto`] sub-check.
fn refute_closed_universal(
    arena: &mut TermArena,
    forall_term: TermId,
    config: &SolverConfig,
) -> Result<Option<CheckResult>, SolverError> {
    let (vars, body) = peel_foralls(arena, forall_term);
    if vars.is_empty() {
        return Ok(None);
    }
    let bound: HashSet<SymbolId> = vars.iter().copied().collect();
    // Only a *closed* quantifier-free body is a sentence we can falsify exactly.
    if !body_is_closed_qf(arena, body, &bound) {
        return Ok(None);
    }
    // Substitute each bound variable with a fresh Herbrand constant of its sort, so
    // the ground solver is free to pick the falsifying witness.
    let mut map: HashMap<TermId, TermId> = HashMap::new();
    for &v in &vars {
        let sort = arena.symbol(v).1;
        let fresh = arena
            .declare(&format!("!cu_{}", v.index()), sort)
            .map_err(|e| SolverError::Backend(e.to_string()))?;
        let var = arena.var(v);
        let fresh_term = arena.var(fresh);
        map.insert(var, fresh_term);
    }
    let mut memo: HashMap<TermId, TermId> = HashMap::new();
    let instance = replace_subterms(arena, body, &map, &mut memo)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    let negated = arena
        .not(instance)
        .map_err(|e| SolverError::Backend(e.to_string()))?;
    // `¬body[c⃗]` satisfiable ⇒ `∃x⃗. ¬body` ⇒ `∀x⃗. body` is false ⇒ query unsat.
    match check_auto(arena, &[negated], config)? {
        CheckResult::Sat(_) => Ok(Some(CheckResult::Unsat)),
        _ => Ok(None),
    }
}

/// Whether `term` is quantifier-free and every symbol it mentions is in `bound`
/// (so the universal it bodies is a closed sentence over exactly `bound`).
fn body_is_closed_qf(arena: &TermArena, term: TermId, bound: &HashSet<SymbolId>) -> bool {
    let mut seen: HashSet<TermId> = HashSet::new();
    let mut stack = vec![term];
    while let Some(t) = stack.pop() {
        if !seen.insert(t) {
            continue;
        }
        match arena.node(t) {
            TermNode::Symbol(s) if !bound.contains(s) => {
                return false; // a free symbol: not a closed sentence
            }
            TermNode::App { op, args } => {
                // Reject anything carrying a *free* symbol the substitution cannot
                // reach: an inner quantifier (not quantifier-free) or an
                // uninterpreted-function application (its `FuncId` is a free symbol
                // — `∀x. f(x)=c` is satisfiable, not a refutable closed sentence).
                if matches!(op, Op::Forall(_) | Op::Exists(_) | Op::Apply(_)) {
                    return false;
                }
                for &a in args {
                    stack.push(a);
                }
            }
            _ => {}
        }
    }
    true
}

/// Infers a trigger: a set of function-application subterms whose bound variables
/// together cover all of them. Prefers a single term that covers everything (e.g.
/// `f(x)`, `g(x, y)`); otherwise a greedy set cover yields a multi-pattern (e.g.
/// `{f(x), g(y)}` for `∀x,y. f(x) = g(y)`). Returns empty when the variables cannot
/// be covered by function applications.
fn select_triggers(arena: &TermArena, body: TermId, vars: &HashMap<SymbolId, u32>) -> Vec<TermId> {
    // Candidate function-application subterms with the variable-index set each one
    // covers.
    let mut candidates: Vec<(TermId, HashSet<u32>)> = Vec::new();
    collect_app_candidates(arena, body, vars, &mut candidates);

    let all: HashSet<u32> = (0..u32::try_from(vars.len()).expect("var count fits u32")).collect();
    // A single covering term is the best trigger.
    if let Some((t, _)) = candidates.iter().find(|(_, c)| *c == all) {
        return vec![*t];
    }
    // Greedy set cover otherwise.
    let mut uncovered = all;
    let mut chosen = Vec::new();
    while !uncovered.is_empty() {
        let best = candidates
            .iter()
            .max_by_key(|(_, c)| c.intersection(&uncovered).count());
        match best {
            Some((t, c)) if c.intersection(&uncovered).next().is_some() => {
                for v in c {
                    uncovered.remove(v);
                }
                chosen.push(*t);
            }
            _ => return Vec::new(), // some variable is in no function application
        }
    }
    chosen
}

/// Collects every function-application subterm of `body`, with the set of bound
/// variable indices it mentions (only those covering ≥1 bound variable are kept).
fn collect_app_candidates(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    out: &mut Vec<(TermId, HashSet<u32>)>,
) {
    if let TermNode::App { op, args } = arena.node(term) {
        if matches!(op, Op::Apply(_)) {
            let mut seen = HashSet::new();
            collect_vars(arena, term, vars, &mut seen);
            if !seen.is_empty() {
                let indices: HashSet<u32> = seen.iter().map(|s| vars[s]).collect();
                out.push((term, indices));
            }
        }
        let args = args.clone();
        for a in args {
            collect_app_candidates(arena, a, vars, out);
        }
    }
}

/// Merges two partial substitutions, returning `None` on a variable conflict.
fn merge_substitutions(
    a: &[Option<ENodeId>],
    b: &[Option<ENodeId>],
) -> Option<Vec<Option<ENodeId>>> {
    let mut out = a.to_vec();
    for (slot, &bi) in out.iter_mut().zip(b) {
        if let Some(bv) = bi {
            match *slot {
                Some(av) if av != bv => return None,
                _ => *slot = Some(bv),
            }
        }
    }
    Some(out)
}

/// Records which `vars` occur in `term`.
fn collect_vars(
    arena: &TermArena,
    term: TermId,
    vars: &HashMap<SymbolId, u32>,
    seen: &mut std::collections::HashSet<SymbolId>,
) {
    match arena.node(term) {
        TermNode::Symbol(s) if vars.contains_key(s) => {
            seen.insert(*s);
        }
        TermNode::App { args, .. } => {
            let args = args.clone();
            for a in args {
                collect_vars(arena, a, vars, seen);
            }
        }
        _ => {}
    }
}

/// Bridges ground IR terms to the e-graph for instantiation: it builds e-nodes,
/// assigns each symbol/function/constant a `decl`, and remembers a representative
/// ground term per class (to substitute back on a match).
struct InstBridge {
    egraph: EGraph,
    term_to_node: HashMap<TermId, ENodeId>,
    func_decls: HashMap<FuncId, u32>,
    symbol_decls: HashMap<usize, u32>,
    op_decls: HashMap<String, u32>,
    /// First ground term seen per class root — the instantiation witness.
    repr_term: HashMap<ENodeId, TermId>,
    next_decl: u32,
}

impl InstBridge {
    fn new() -> Self {
        Self {
            egraph: EGraph::new(),
            term_to_node: HashMap::new(),
            func_decls: HashMap::new(),
            symbol_decls: HashMap::new(),
            op_decls: HashMap::new(),
            repr_term: HashMap::new(),
            next_decl: 0,
        }
    }

    fn fresh_decl(&mut self) -> u32 {
        let d = self.next_decl;
        self.next_decl += 1;
        d
    }

    fn add_term(&mut self, arena: &TermArena, term: TermId) -> ENodeId {
        if let Some(&n) = self.term_to_node.get(&term) {
            return n;
        }
        let node = match arena.node(term) {
            TermNode::Symbol(s) => {
                let decl = self.symbol_decl(s.index());
                self.egraph.add(decl, &[])
            }
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.func_decl(func);
                self.egraph.add(decl, &children)
            }
            TermNode::App { op, args } => {
                // Other interpreted operators are treated as uninterpreted for the
                // purposes of matching (sound: matching only fires on real terms).
                let op = format!("{op:?}");
                let args = args.clone();
                let children: Vec<ENodeId> =
                    args.iter().map(|&a| self.add_term(arena, a)).collect();
                let decl = self.op_decl(&op);
                self.egraph.add(decl, &children)
            }
            _ => {
                // A literal constant: each distinct value is its own leaf.
                let key = format!("c:{:?}", arena.node(term));
                let decl = self.op_decl(&key);
                self.egraph.add(decl, &[])
            }
        };
        let root = self.egraph.root(node);
        self.repr_term.entry(root).or_insert(term);
        self.term_to_node.insert(term, node);
        node
    }

    fn symbol_decl(&mut self, sym: usize) -> u32 {
        if let Some(&d) = self.symbol_decls.get(&sym) {
            return d;
        }
        let d = self.fresh_decl();
        self.symbol_decls.insert(sym, d);
        d
    }

    fn func_decl(&mut self, func: FuncId) -> u32 {
        if let Some(&d) = self.func_decls.get(&func) {
            return d;
        }
        let d = self.fresh_decl();
        self.func_decls.insert(func, d);
        d
    }

    fn op_decl(&mut self, key: &str) -> u32 {
        if let Some(&d) = self.op_decls.get(key) {
            return d;
        }
        let d = self.fresh_decl();
        self.op_decls.insert(key.to_owned(), d);
        d
    }

    /// Converts a trigger term to an e-matching [`Pattern`] under this bridge's
    /// decl assignment: the bound `var` becomes `Var(0)`, and every other subterm
    /// (symbols, applications, constants, interpreted ops) becomes an application
    /// keyed by the same decl the ground terms use — so a ground subterm in the
    /// trigger matches its own class, while only `var` is free.
    fn trigger_to_pattern(
        &mut self,
        arena: &TermArena,
        term: TermId,
        vars: &HashMap<SymbolId, u32>,
    ) -> Pattern {
        match arena.node(term) {
            TermNode::Symbol(s) if vars.contains_key(s) => Pattern::Var(vars[s]),
            TermNode::Symbol(s) => Pattern::App(self.symbol_decl(s.index()), Vec::new()),
            TermNode::App {
                op: Op::Apply(func),
                args,
            } => {
                let func = *func;
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.func_decl(func), subs)
            }
            TermNode::App { op, args } => {
                let key = format!("{op:?}");
                let args = args.clone();
                let subs = args
                    .iter()
                    .map(|&a| self.trigger_to_pattern(arena, a, vars))
                    .collect();
                Pattern::App(self.op_decl(&key), subs)
            }
            _ => Pattern::App(
                self.op_decl(&format!("c:{:?}", arena.node(term))),
                Vec::new(),
            ),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use axeyum_ir::Sort;

    /// Builds `∀x. (= (f x) c)` and ground terms mentioning `f(a)`, `f(b)`.
    #[allow(clippy::many_single_char_names)]
    fn setup() -> (
        TermArena,
        TermId,
        [TermId; 2],
        TermId,
        TermId,
        FuncId,
        SymbolId,
    ) {
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        // A ground assertion that contains f(a) and f(b).
        let sum = arena.bv_add(fa, fb).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        // Body referencing the bound variable: (= (f x) c).
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        (arena, forall, [a, b], c, ground0, f, x)
    }

    #[test]
    fn instantiates_over_ground_applications() {
        let (mut arena, forall, [a, b], c, ground0, f, _x) = setup();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);

        // Expect (= (f a) c) and (= (f b) c).
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let want_a = arena.eq(fa, c).unwrap();
        let want_b = arena.eq(fb, c).unwrap();
        assert!(instances.contains(&want_a), "instance for a missing");
        assert!(instances.contains(&want_b), "instance for b missing");
        assert_eq!(instances.len(), 2);
    }

    #[test]
    fn witness_tuples_expose_the_matched_witnesses() {
        // The witness-tuple variant returns the binder→ground-term tuples (in
        // binder order) the e-matching selects: here `[a]` and `[b]` for the two
        // f-applications. This is what the Alethe quantifier emitter consumes.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let (vars, _body, tuples) =
            witness_tuples_via_egraph(&mut arena, &[ground0], forall).expect("matches");
        assert_eq!(vars.len(), 1, "one binder");
        assert!(tuples.contains(&vec![a]), "witness a missing: {tuples:?}");
        assert!(tuples.contains(&vec![b]), "witness b missing: {tuples:?}");
        assert_eq!(tuples.len(), 2);
    }

    #[test]
    fn instantiation_is_modulo_congruence() {
        // Add a = b to the ground: f(a) and f(b) become one class, so the trigger
        // fires once and there is a single instance.
        let (mut arena, forall, [a, b], _c, ground0, _f, _x) = setup();
        let a_eq_b = arena.eq(a, b).unwrap();
        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0, a_eq_b], forall);
        assert_eq!(
            instances.len(),
            1,
            "congruent f-applications instantiate once, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_nested_trigger() {
        // ∀x. (= (f (g x)) c), ground containing f(g(a)): instance (= (f (g a)) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let ga = arena.apply(g, &[a]).unwrap();
        let fga = arena.apply(f, &[ga]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(fga, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let gx = arena.apply(g, &[xv]).unwrap();
        let fgx = arena.apply(f, &[gx]).unwrap();
        let body = arena.eq(fgx, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(fga, c).unwrap();
        assert_eq!(instances, vec![want], "nested trigger f(g(x)) → x = a");
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_over_a_binary_trigger_with_a_ground_argument() {
        // ∀x. (= (h x a) c), ground containing h(b, a) and h(d, a): two instances;
        // the ground argument `a` in the trigger is matched by its class.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let d = arena.bv_var("d", 8).unwrap();
        let h = arena.declare_fun("h", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let hba = arena.apply(h, &[b, a]).unwrap();
        let hda = arena.apply(h, &[d, a]).unwrap();
        // A decoy h(a, b) whose ground argument is b, not a — must NOT match h(x, a).
        let hab = arena.apply(h, &[a, b]).unwrap();
        let hba_hda = arena.bv_add(hba, hda).unwrap();
        let sum = arena.bv_add(hba_hda, hab).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(sum, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let hxa = arena.apply(h, &[xv, a]).unwrap();
        let body = arena.eq(hxa, c).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want_b = arena.eq(hba, c).unwrap();
        let want_d = arena.eq(hda, c).unwrap();
        assert!(instances.contains(&want_b));
        assert!(instances.contains(&want_d));
        assert_eq!(
            instances.len(),
            2,
            "only h(_, a) matches, got {instances:?}"
        );
    }

    #[test]
    #[allow(clippy::many_single_char_names, clippy::similar_names)]
    fn instantiates_a_multi_pattern_trigger() {
        // ∀x. ∀y. (= (f x) (g y)): no single subterm covers both x and y, so the
        // multi-pattern {f(x), g(y)} is inferred and the matches joined.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let gb = arena.apply(g, &[b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let g0 = arena.eq(fa, zero).unwrap();
        let g1 = arena.eq(gb, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gy = arena.apply(g, &[yv]).unwrap();
        let inner_body = arena.eq(fx, gy).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[g0, g1], forall);
        let want = arena.eq(fa, gb).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b joined from {{f(x), g(y)}}");
    }

    #[test]
    #[allow(clippy::similar_names, clippy::many_single_char_names)]
    fn nested_trigger_fires_through_congruence_involution() {
        // The canonical congruence-only test: ∀x. f(f(x)) = x with ground
        //   f(a) = b,  f(b) = c,  a ≠ c.
        // The trigger f(f(x)) has NO syntactic match — there is no literal
        // `f(f(·))` ground term. It fires only because f(a)=b puts f(a) inside b's
        // class, so the outer ground f(b) has an inner f-application (f(a)) in its
        // argument class ⇒ x ↦ a. The instance f(f(a)) = a forces c = a ⨯ a ≠ c.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let c = arena.bv_var("c", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fb = arena.apply(f, &[b]).unwrap();
        let fa_eq_b = arena.eq(fa, b).unwrap();
        let fb_eq_c = arena.eq(fb, c).unwrap();
        let a_ne_c = {
            let e = arena.eq(a, c).unwrap();
            arena.not(e).unwrap()
        };

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let ffx = arena.apply(f, &[fx]).unwrap();
        let body = arena.eq(ffx, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_eq_b, fb_eq_c, a_ne_c, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "nested trigger must fire via congruence and refute"
        );
    }

    #[test]
    #[allow(clippy::similar_names)]
    fn instantiation_loop_refutes_a_quantified_contradiction() {
        // f(a) ≠ 0  ∧  ∀x. (= (f x) 0): instantiating x = a gives f(a) = 0,
        // contradicting the ground disequality → UNSAT.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa_eq_0 = arena.eq(fa, zero).unwrap();
        let fa_ne_0 = arena.not(fa_eq_0).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let fx_eq_0 = arena.eq(fx, zero).unwrap();
        let forall = arena.forall(x, fx_eq_0).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(result, CheckResult::Unsat);
    }

    #[test]
    #[allow(clippy::similar_names, clippy::many_single_char_names)]
    fn instantiation_loop_refutes_across_multiple_rounds() {
        // A genuinely multi-round refutation: the g(x) trigger can only fire after
        // the f(x) instantiation has introduced g(a) into the ground set.
        //   ground:    f(a) ≠ 0
        //   ∀x. f(x) = g(x)   → round 1: f(a) = g(a)  (introduces ground g(a))
        //   ∀x. g(x) = 0      → round 2: g(a) = 0     (now g(a) exists to match)
        //   ⇒ f(a) = g(a) = 0 contradicts f(a) ≠ 0   → UNSAT (round 3 check)
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let g = arena.declare_fun("g", &[sort], sort).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let fa = arena.apply(f, &[a]).unwrap();
        let fa_ne_0 = {
            let e = arena.eq(fa, zero).unwrap();
            arena.not(e).unwrap()
        };

        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let gx = arena.apply(g, &[xv]).unwrap();
        let fx_eq_gx = arena.eq(fx, gx).unwrap();
        let forall_fg = arena.forall(x, fx_eq_gx).unwrap();
        let gx_eq_0 = arena.eq(gx, zero).unwrap();
        let forall_g0 = arena.forall(x, gx_eq_0).unwrap();

        let result = prove_quantified_unsat_via_egraph(
            &mut arena,
            &[fa_ne_0, forall_fg, forall_g0],
            &SolverConfig::default(),
        )
        .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "multi-round chaining should refute"
        );
    }

    #[test]
    fn instantiation_loop_passes_through_quantifier_free() {
        // No universals: routes straight to check_auto (here, sat).
        let mut arena = TermArena::new();
        let a = arena.bv_var("a", 8).unwrap();
        let one = arena.bv_const(8, 1).unwrap();
        let a_eq_1 = arena.eq(a, one).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[a_eq_1], &SolverConfig::default())
                .unwrap();
        assert!(matches!(result, CheckResult::Sat(_)));
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn instantiates_a_two_variable_quantifier() {
        // ∀x. ∀y. (= (g x y) c), ground containing g(a, b): instance (= (g a b) c).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let a = arena.bv_var("a", 8).unwrap();
        let b = arena.bv_var("b", 8).unwrap();
        let g = arena.declare_fun("g", &[sort, sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let gab = arena.apply(g, &[a, b]).unwrap();
        let zero = arena.bv_const(8, 0).unwrap();
        let ground0 = arena.eq(gab, zero).unwrap();

        let x = arena.declare("x", sort).unwrap();
        let y = arena.declare("y", sort).unwrap();
        let xv = arena.var(x);
        let yv = arena.var(y);
        let gxy = arena.apply(g, &[xv, yv]).unwrap();
        let inner_body = arena.eq(gxy, c).unwrap();
        let inner = arena.forall(y, inner_body).unwrap();
        let forall = arena.forall(x, inner).unwrap();

        let instances = instantiate_forall_via_egraph(&mut arena, &[ground0], forall);
        let want = arena.eq(gab, c).unwrap();
        assert_eq!(instances, vec![want], "x↦a, y↦b from the g(x,y) trigger");
    }

    #[test]
    #[allow(clippy::many_single_char_names)]
    fn closed_universal_with_no_trigger_is_refuted() {
        // The measured qbv-simp shape: ∀A B C D. (A=B ∧ C=D) ∨ (A=C ∧ B=D).
        // status unsat — the universal is *false* (A=0,B=1,C=0,D=0 falsifies it),
        // but its body has no function-application trigger, so the e-matching loop
        // alone returns `unknown`. Closed-universal falsification decides it.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let mk = |arena: &mut TermArena, n: &str| {
            let s = arena.declare(n, sort).unwrap();
            (s, arena.var(s))
        };
        let (a, av) = mk(&mut arena, "A");
        let (b, bv) = mk(&mut arena, "B");
        let (c, cv) = mk(&mut arena, "C");
        let (d, dv) = mk(&mut arena, "D");
        let ab = arena.eq(av, bv).unwrap();
        let cd = arena.eq(cv, dv).unwrap();
        let ac = arena.eq(av, cv).unwrap();
        let bd = arena.eq(bv, dv).unwrap();
        let left = arena.and(ab, cd).unwrap();
        let right = arena.and(ac, bd).unwrap();
        let body = arena.or(left, right).unwrap();
        // Bind innermost-first so the peeled prefix is [A, B, C, D].
        let mut forall = arena.forall(d, body).unwrap();
        forall = arena.forall(c, forall).unwrap();
        forall = arena.forall(b, forall).unwrap();
        forall = arena.forall(a, forall).unwrap();

        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                .unwrap();
        assert_eq!(
            result,
            CheckResult::Unsat,
            "a false closed universal with no trigger must be refuted"
        );
    }

    #[test]
    fn valid_closed_universal_is_not_refuted() {
        // ∀x. (x = x): valid (true), must NOT be reported unsat. The falsification
        // sub-check `¬(x=x)` is unsat, so the lever declines and the loop reaches
        // its own (non-unsat) verdict.
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let body = arena.eq(xv, xv).unwrap();
        let forall = arena.forall(x, body).unwrap();
        let result =
            prove_quantified_unsat_via_egraph(&mut arena, &[forall], &SolverConfig::default())
                .unwrap();
        assert_ne!(
            result,
            CheckResult::Unsat,
            "a valid closed universal must never be refuted"
        );
    }

    #[test]
    fn open_universal_is_not_treated_as_closed() {
        // ∀x. (f x) = c has a free function symbol `f` — it is NOT a closed
        // sentence, so `body_is_closed_qf` rejects it and the falsification lever
        // does not fire (the e-matching path owns it).
        let mut arena = TermArena::new();
        let sort = Sort::BitVec(8);
        let f = arena.declare_fun("f", &[sort], sort).unwrap();
        let c = arena.bv_const(8, 5).unwrap();
        let x = arena.declare("x", sort).unwrap();
        let xv = arena.var(x);
        let fx = arena.apply(f, &[xv]).unwrap();
        let body = arena.eq(fx, c).unwrap();
        let bound: HashSet<SymbolId> = std::iter::once(x).collect();
        assert!(
            !body_is_closed_qf(&arena, body, &bound),
            "a body mentioning a free function symbol is not closed"
        );
    }

    #[test]
    fn non_forall_or_no_trigger_yields_nothing() {
        let mut arena = TermArena::new();
        let p = arena.bool_var("p").unwrap();
        // Not a forall.
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], p).is_empty());
        // A forall whose body has no unary trigger over the bound variable.
        let x = arena.declare("x", Sort::Bool).unwrap();
        let xv = arena.var(x);
        let body = arena.or(xv, p).unwrap();
        let forall = arena.forall(x, body).unwrap();
        assert!(instantiate_forall_via_egraph(&mut arena, &[p], forall).is_empty());
    }
}
